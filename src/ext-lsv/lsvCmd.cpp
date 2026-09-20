#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"

#include <cstdint>
#include <cstdlib>
#include <unordered_map>
#include <utility>
#include <vector>

ABC_NAMESPACE_IMPL_START

static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_tt", Lsv_CommandCutTt, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_cut_bddsize", Lsv_CommandCutBddSize, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

////////////////////////////////////////////////////////////////////////
///                     Cut enumeration helpers                      ///
////////////////////////////////////////////////////////////////////////

using Lsv_Cut = std::vector<int>;

static bool Lsv_CutDominates(const Lsv_Cut& a, const Lsv_Cut& b) {
  // a dominates b iff a is a subset of b
  if (a.size() > b.size()) return false;
  size_t i = 0, j = 0;
  while (i < a.size() && j < b.size()) {
    if (a[i] == b[j]) {
      ++i;
      ++j;
    } else if (a[i] > b[j]) {
      ++j;
    } else {
      return false;
    }
  }
  return i == a.size();
}

static Lsv_Cut Lsv_CutMerge(const Lsv_Cut& a, const Lsv_Cut& b) {
  Lsv_Cut r;
  r.reserve(a.size() + b.size());
  size_t i = 0, j = 0;
  while (i < a.size() && j < b.size()) {
    if (a[i] < b[j])
      r.push_back(a[i++]);
    else if (a[i] > b[j])
      r.push_back(b[j++]);
    else {
      r.push_back(a[i]);
      ++i;
      ++j;
    }
  }
  while (i < a.size()) r.push_back(a[i++]);
  while (j < b.size()) r.push_back(b[j++]);
  return r;
}

static void Lsv_CutSetAdd(std::vector<Lsv_Cut>& cuts, const Lsv_Cut& cut) {
  for (const auto& c : cuts) {
    if (c == cut) return;
    if (Lsv_CutDominates(c, cut)) return;  // existing cut dominates new
  }
  // remove cuts dominated by the new cut
  std::vector<Lsv_Cut> kept;
  kept.reserve(cuts.size() + 1);
  for (auto& c : cuts) {
    if (!Lsv_CutDominates(cut, c)) kept.push_back(std::move(c));
  }
  kept.push_back(cut);
  cuts.swap(kept);
}

static std::vector<std::vector<Lsv_Cut>> Lsv_NtkEnumerateCuts(Abc_Ntk_t* pNtk,
                                                             int nK) {
  const int nObjs = Abc_NtkObjNumMax(pNtk);
  std::vector<std::vector<Lsv_Cut>> cuts(nObjs);

  Abc_Obj_t* pObj;
  int i;

  // Primary inputs: only the trivial cut
  Abc_NtkForEachCi(pNtk, pObj, i) {
    int id = (int)Abc_ObjId(pObj);
    cuts[id].push_back(Lsv_Cut{id});
  }

  // Constant node (if present): trivial cut
  pObj = Abc_AigConst1(pNtk);
  if (pObj) {
    int id = (int)Abc_ObjId(pObj);
    cuts[id].push_back(Lsv_Cut{id});
  }

  // AND nodes in topological order (object ID order for strashed AIGs)
  Abc_NtkForEachNode(pNtk, pObj, i) {
    const int id = Abc_ObjId(pObj);
    Abc_Obj_t* pFan0 = Abc_ObjFanin0(pObj);
    Abc_Obj_t* pFan1 = Abc_ObjFanin1(pObj);
    const auto& cuts0 = cuts[Abc_ObjId(pFan0)];
    const auto& cuts1 = cuts[Abc_ObjId(pFan1)];

    // trivial cut
    Lsv_CutSetAdd(cuts[id], Lsv_Cut{id});

    for (const auto& c0 : cuts0) {
      for (const auto& c1 : cuts1) {
        Lsv_Cut merged = Lsv_CutMerge(c0, c1);
        if ((int)merged.size() <= nK) Lsv_CutSetAdd(cuts[id], merged);
      }
    }
  }

  return cuts;
}

////////////////////////////////////////////////////////////////////////
///                     Truth-table computation                      ///
////////////////////////////////////////////////////////////////////////

static int Lsv_EvalNodeValue(Abc_Obj_t* pObj,
                             const std::unordered_map<int, int>& leafVal,
                             std::unordered_map<int, int>& memo) {
  const int id = Abc_ObjId(pObj);
  auto lit = leafVal.find(id);
  if (lit != leafVal.end()) return lit->second;

  auto it = memo.find(id);
  if (it != memo.end()) return it->second;

  assert(Abc_ObjIsNode(pObj));
  int v0 = Lsv_EvalNodeValue(Abc_ObjFanin0(pObj), leafVal, memo);
  int v1 = Lsv_EvalNodeValue(Abc_ObjFanin1(pObj), leafVal, memo);
  if (Abc_ObjFaninC0(pObj)) v0 ^= 1;
  if (Abc_ObjFaninC1(pObj)) v1 ^= 1;
  int res = v0 & v1;
  memo[id] = res;
  return res;
}

static uint64_t Lsv_CutTruthTable(Abc_Obj_t* pRoot, const Lsv_Cut& cut) {
  const int n = (int)cut.size();
  const uint64_t nMinterms = 1ULL << n;
  uint64_t tt = 0;

  for (uint64_t p = 0; p < nMinterms; ++p) {
    std::unordered_map<int, int> leafVal;
    leafVal.reserve(n * 2);
    for (int j = 0; j < n; ++j) {
      // First leaf is the MSB of the assignment index
      int bit = (int)((p >> (n - 1 - j)) & 1ULL);
      leafVal[cut[j]] = bit;
    }
    std::unordered_map<int, int> memo;
    int val = Lsv_EvalNodeValue(pRoot, leafVal, memo);
    if (val) tt |= (1ULL << p);
  }
  return tt;
}

static void Lsv_PrintHexTt(uint64_t tt) {
  // Uppercase hex without leading zeros (except for 0)
  printf("%lX", (unsigned long)tt);
}

////////////////////////////////////////////////////////////////////////
///                        BDD computation                           ///
////////////////////////////////////////////////////////////////////////

static DdNode* Lsv_BuildCutBdd(DdManager* dd, Abc_Obj_t* pObj,
                               const std::unordered_map<int, int>& leaf2var,
                               std::unordered_map<int, DdNode*>& memo) {
  const int id = Abc_ObjId(pObj);
  auto lit = leaf2var.find(id);
  if (lit != leaf2var.end()) {
    return Cudd_bddIthVar(dd, lit->second);
  }

  auto it = memo.find(id);
  if (it != memo.end()) return it->second;

  assert(Abc_ObjIsNode(pObj));
  DdNode* f0 = Lsv_BuildCutBdd(dd, Abc_ObjFanin0(pObj), leaf2var, memo);
  DdNode* f1 = Lsv_BuildCutBdd(dd, Abc_ObjFanin1(pObj), leaf2var, memo);
  if (Abc_ObjFaninC0(pObj)) f0 = Cudd_Not(f0);
  if (Abc_ObjFaninC1(pObj)) f1 = Cudd_Not(f1);

  DdNode* res = Cudd_bddAnd(dd, f0, f1);
  Cudd_Ref(res);
  memo[id] = res;
  return res;
}

static int Lsv_CutBddSize(Abc_Obj_t* pRoot, const Lsv_Cut& cut) {
  const int n = (int)cut.size();
  DdManager* dd = Cudd_Init(n, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
  Cudd_AutodynDisable(dd);

  std::unordered_map<int, int> leaf2var;
  leaf2var.reserve(n * 2);
  // Smaller node ID -> smaller BDD variable index -> closer to root
  for (int j = 0; j < n; ++j) leaf2var[cut[j]] = j;

  std::unordered_map<int, DdNode*> memo;
  DdNode* bFunc = Lsv_BuildCutBdd(dd, pRoot, leaf2var, memo);
  Cudd_Ref(bFunc);
  int size = Cudd_DagSize(bFunc);

  for (auto& kv : memo) Cudd_RecursiveDeref(dd, kv.second);
  Cudd_RecursiveDeref(dd, bFunc);
  Cudd_Quit(dd);
  return size;
}

static void Lsv_PrintCutLeaves(const Lsv_Cut& cut) {
  for (size_t i = 0; i < cut.size(); ++i) {
    if (i) printf(" ");
    printf("%d", cut[i]);
  }
}

////////////////////////////////////////////////////////////////////////
///                         Command handlers                         ///
////////////////////////////////////////////////////////////////////////

void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    Abc_Obj_t* pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
             Abc_ObjName(pFanin));
    }
    if (Abc_NtkHasSop(pNtk)) {
      printf("The SOP of this node:\n%s", (char*)pObj->pData);
    }
  }
}

int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintNodes(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

int Lsv_CommandCutTt(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c, nK = 0;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (globalUtilOptind >= argc) goto usage;
  {
    char* end = nullptr;
    long k = strtol(argv[globalUtilOptind], &end, 10);
    if (end == argv[globalUtilOptind] || *end != '\0' || k < 1) goto usage;
    nK = (int)k;
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "LSV cut commands only work for structurally hashed AIGs (run \"strash\").\n");
    return 1;
  }

  {
    auto allCuts = Lsv_NtkEnumerateCuts(pNtk, nK);
    Abc_Obj_t* pObj;
    int i;
    Abc_NtkForEachNode(pNtk, pObj, i) {
      const int id = Abc_ObjId(pObj);
      for (const auto& cut : allCuts[id]) {
        printf("%d: ", id);
        Lsv_PrintCutLeaves(cut);
        printf(": ");
        Lsv_PrintHexTt(Lsv_CutTruthTable(pObj, cut));
        printf("\n");
      }
    }
  }
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_tt <k>\n");
  Abc_Print(-2, "\t        enumerate k-feasible cuts and print truth tables\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

int Lsv_CommandCutBddSize(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c, nK = 0;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (globalUtilOptind >= argc) goto usage;
  {
    char* end = nullptr;
    long k = strtol(argv[globalUtilOptind], &end, 10);
    if (end == argv[globalUtilOptind] || *end != '\0' || k < 1) goto usage;
    nK = (int)k;
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "LSV cut commands only work for structurally hashed AIGs (run \"strash\").\n");
    return 1;
  }

  {
    auto allCuts = Lsv_NtkEnumerateCuts(pNtk, nK);
    Abc_Obj_t* pObj;
    int i;
    Abc_NtkForEachNode(pNtk, pObj, i) {
      const int id = Abc_ObjId(pObj);
      for (const auto& cut : allCuts[id]) {
        printf("%d: ", id);
        Lsv_PrintCutLeaves(cut);
        printf(": %d\n", Lsv_CutBddSize(pObj, cut));
      }
    }
  }
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_cut_bddsize <k>\n");
  Abc_Print(-2, "\t        enumerate k-feasible cuts and print ROBDD sizes\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

ABC_NAMESPACE_IMPL_END
