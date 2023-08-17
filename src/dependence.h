#include <llvm/ADT/ArrayRef.h>
#include <vector>

#include "llvm/ADT/ArrayRef.h"
#include "mlir/Analysis/Presburger/PresburgerRelation.h"
#include "mlir/Analysis/Presburger/PresburgerSpace.h"
#include "mlir/Analysis/Presburger/Simplex.h"

using llvm::ArrayRef;
using mlir::presburger::PresburgerSpace;
using mlir::presburger::PresburgerRelation;
using mlir::presburger::PresburgerSet;
using mlir::presburger::SymbolicLexOpt;

class DependenceAnalysis {
  private:
    PresburgerRelation sink;
    ArrayRef<PresburgerRelation> mustSources, maySources;
    // mustNoSource = mustdo, mayNoSource = maydo
    PresburgerSet mustNoSource, mayNoSource;
    struct {
      std::vector<PresburgerRelation> mustSourceMustDeps, mustSourceMayDeps,
        maySourceMayDeps;
    } depMaps;

    PresburgerRelation lastSource(PresburgerSet& set_C, PresburgerRelation source, unsigned level);
    bool intermediateSources(std::vector<PresburgerRelation>& sources, unsigned j, unsigned level);
    PresburgerRelation allSources(PresburgerSet &set_C, unsigned j, unsigned level);
    PresburgerRelation allIntermediateSources(std::vector<PresburgerRelation>, std::vector<PresburgerRelation>, unsigned, unsigned);
    PresburgerRelation lastLaterSource(PresburgerRelation curJDeps, int j, int afterLevel, int k, int sinkLevel, PresburgerSet &trest);
    PresburgerRelation allLaterSources(std::vector<PresburgerRelation> mustDeps, std::vector<PresburgerRelation> mayDeps, unsigned j, unsigned level);
  public:
    DependenceAnalysis(PresburgerRelation sink, ArrayRef<PresburgerRelation> maySources,
        ArrayRef<PresburgerRelation> mustSources) : sink(sink),
    mustSources(mustSources), maySources(maySources),
    mustNoSource(PresburgerSet::getEmpty(sink.getSpace().getDomainSpace())),
    mayNoSource(PresburgerSet::getEmpty(sink.getSpace().getDomainSpace())) {
      // mustNoSource initially has all of sink's domain
      for(auto ir : sink.getAllDisjuncts()) {
        mustNoSource.unionInPlace(ir.getDomainSet());
      }
      for(int i = 0, sz = mustSources.size(); i < sz; i++) {
        PresburgerSpace s = PresburgerSpace::getRelationSpace(mustSources[i].getNumDomainVars(), sink.getNumDomainVars());
        depMaps.mustSourceMustDeps.push_back(PresburgerRelation::getEmpty(s));
        depMaps.mustSourceMayDeps.push_back(PresburgerRelation::getEmpty(s));
      }
      for(int i = 0, sz = maySources.size(); i < sz; i++) {
        PresburgerSpace s = PresburgerSpace::getRelationSpace(mustSources[i].getNumDomainVars(), sink.getNumDomainVars());
        depMaps.maySourceMayDeps.push_back(PresburgerRelation::getEmpty(s));
      }
    }
    void compute();
    PresburgerSet *getMustNoSource();
    PresburgerSet *getMayNoSource();
    PresburgerRelation *getDepMap();
};
