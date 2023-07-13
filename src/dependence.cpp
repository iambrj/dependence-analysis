#include "dependence.h"
#include "mlir/Analysis/Presburger/PresburgerRelation.h"
#include "mlir/Analysis/Presburger/PresburgerSpace.h"

void DataflowAnalysis::compute() {
  unsigned depth = 2 * sink.getNumDomainVars() + 1;
  for(unsigned level = depth; level >= 1; level--) {
    std::vector<PresburgerRelation> mustDeps, mayDeps;
    for(unsigned j = mustSources.size() - 1; j >= 0; j--) {
      PresburgerSpace s = PresburgerSpace::getRelationSpace(sink.getNumDomainVars(), mustSources[j].getNumRangeVars());
      mustDeps.push_back(PresburgerRelation::getEmpty(s));
      mayDeps.push_back(PresburgerRelation::getEmpty(s));
    }

    unsigned j = mustSources.size() - 1;
    for(; j >= 0; j--) {
      // TODO: If mustSources[j] cannot precede sink at this level continue
      PresburgerRelation T = lastSource(mustNoSource, mustSources[j], level);
      mustDeps[j].unionInPlace(T);

      if(!intermediateSources(mustDeps, j, level)) {
        // TODO: Error
      }

      T = lastSource(mayNoSource, mustSources[j], level);
      mayDeps[j].unionInPlace(T);

      if(!intermediateSources(mayDeps, j, level)) {
        // TODO: Error
      }

      if(mustNoSource.isIntegerEmpty() && mayNoSource.isIntegerEmpty()) {
        break;
      }
    }

    for(; j >= 0; j--) {
      // TODO: If mustSources[j] cannot precede sink at this level continue
      if(!intermediateSources(mustDeps, j, level)) {
        // TODO: Error
      }
      if(!intermediateSources(mayDeps, j, level)) {
        // TODO: Error
      }
    }

    for(j = 0; j < maySources.size(); j++) {
      // TODO: If maySources[j] cannot precede sink at this level continue
      PresburgerRelation T = allSources(0, j, level);
      depMaps.maySourceMayDeps[j].unionInPlace(T);
      T = allSources(1, j, level);
      depMaps.maySourceMayDeps[j].unionInPlace(T);
      PresburgerSet foundMayDeps = PresburgerSet::getEmpty(T.getSpace().getRangeSpace());
      for(auto ir : T.getAllDisjuncts()) {
        foundMayDeps.unionInPlace(ir.getRangeSet());
      }
      mustNoSource.subtract(foundMayDeps);
      mayNoSource.unionInPlace(foundMayDeps);

      depMaps.maySourceMayDeps[j] = allIntermediateSources(mustDeps, mayDeps, j, level);
    }

    for(j = mustSources.size(); j >= 0; j--) {
      depMaps.mustSourceMustDeps[j].unionInPlace(mustDeps[j]);
      depMaps.mustSourceMayDeps[j].unionInPlace(mayDeps[j]);
    }

    if(mustNoSource.isIntegerEmpty() && mayNoSource.isIntegerEmpty()) {
      break;
    }
  }
}

// TODO: update mustNoSource/mayNoSource
PresburgerRelation DataflowAnalysis::lastSource(PresburgerSet& set_c, PresburgerRelation source, unsigned level) {
  source.applyDomain(sink);
  // TODO: filter depMap after and compute lexmax
}

bool DataflowAnalysis::intermediateSources(std::vector<PresburgerRelation>& sinkLevelDeps, unsigned j, unsigned sinkLevel) {
  // TODO: sanity checks
  if(sinkLevelDeps[j].isIntegerEmpty()) {
    return true;
  }
  int depth = 2 * mustSources[j].getNumDomainVars() + 1;
  for(int k = j - 1; k >= 0; k--) {
    // TODO: if sinkLevelDeps[k] cannot occur before sink at sinkLevel continue
    for(int level = sinkLevel; level <= depth; level++) {
      // TODO: if sinkLevelDeps[k] cannot occur before sinkLevelDeps[j] at this level
      // continue
      PresburgerSet trest = PresburgerSet::getEmpty(sinkLevelDeps[j].getSpace().getRangeSpace());
      PresburgerRelation T = lastLaterSource(j, sinkLevel, k, trest);
      if(T.isIntegerEmpty()) {
        continue;
      }
      // TODO: sinkLevelDeps[j] = sinkLevelDeps[j].intersectRange(trest);
      sinkLevelDeps[k].unionInPlace(T);
    }
  }
}

PresburgerRelation DataflowAnalysis::lastLaterSource(int j, int sinkLevel, int k, PresburgerSet empty) {
}

PresburgerRelation DataflowAnalysis::allSources(unsigned must, unsigned j, unsigned level) {
}

PresburgerRelation DataflowAnalysis::allIntermediateSources(std::vector<PresburgerRelation> mustDeps, std::vector<PresburgerRelation> mayDeps, unsigned j, unsigned level) {
  for(int k = 0; k < ; ) {
  }
}

PresburgerRelation DataflowAnalysis::allLaterSources(std::vector<PresburgerRelation> mustDeps, std::vector<PresburgerRelation> mayDeps, unsigned j, unsigned level) {
}
