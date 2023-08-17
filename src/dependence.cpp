#include "dependence.h"
#include "mlir/Analysis/Presburger/IntegerRelation.h"
#include "mlir/Analysis/Presburger/MPInt.h"
#include "mlir/Analysis/Presburger/PresburgerRelation.h"
#include "mlir/Analysis/Presburger/PresburgerSpace.h"
#include "mlir/Analysis/Presburger/Simplex.h"
#include "llvm/ADT/ArrayRef.h"
#include <vector>

void DependenceAnalysis::compute() {
  unsigned depth = 2 * sink.getNumDomainVars() + 1;
  for(unsigned level = depth; level >= 1; level--) {
    std::vector<PresburgerRelation> mustDeps, mayDeps;
    for(unsigned j = mustSources.size() - 1; j >= 0; j--) {
      PresburgerSpace s = PresburgerSpace::getRelationSpace(mustSources[j].getNumDomainVars(), sink.getNumDomainVars());
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

// XXX: upstream this into the PresburgerRelation class?
static PresburgerRelation PREqual(PresburgerSpace space, int tillPos) {
  mlir::presburger::IntegerRelation ir =
    mlir::presburger::IntegerRelation::getUniverse(space);
  for(int i = 0, l = space.getNumDomainVars(); i < l && i < tillPos; i++) {
    std::vector<mlir::presburger::MPInt> vEq(space.getNumDimVars(), mlir::presburger::MPInt(0));
    vEq[i] = 1;
    vEq[space.getNumDomainVars() + i] = -1;
    ir.addEquality(vEq);
  }
  return PresburgerRelation(ir);
}

// XXX: upstream this into the PresburgerRelation class?
static PresburgerRelation PRMoreAt(PresburgerSpace space, int pos) {
  mlir::presburger::IntegerRelation ir =
    mlir::presburger::IntegerRelation::getUniverse(space);
    std::vector<mlir::presburger::MPInt> vIneq(space.getNumDimVars(), mlir::presburger::MPInt(0));
    vIneq[pos] = 1;
    vIneq[space.getNumDomainVars() + pos] = -1;
    ir.addInequality(vIneq);
    return PresburgerRelation(ir);
}

static PresburgerRelation afterAtLevel(PresburgerSpace depSpace, int level) {
  if(level % 2)
    return PREqual(depSpace, level / 2);
  return PRMoreAt(depSpace, level / 2 - 1);
}

// TODO: update mustNoSource/mayNoSource
// Compute the last iterations of a given source before the sink iterations at a
// given level
PresburgerRelation DependenceAnalysis::lastSource(PresburgerSet& set_C, PresburgerRelation source, unsigned level) {
  source.inverse();
  PresburgerRelation depMap = sink, result = PresburgerRelation::getEmpty(PresburgerSpace::getRelationSpace(source.getNumDomainVars(), sink.getNumDomainVars()));
  depMap.compose(source);
  depMap = depMap.intersect(afterAtLevel(depMap.getSpace(), level));
  depMap = depMap.intersectDomain(set_C);
  SymbolicLexOpt lexmax = depMap.findSymbolicIntegerLexMax();
  // XXX: Assert that lexmax's unboudedDomain is empty?
  for(const auto& piece : lexmax.lexopt.getAllPieces()) {
    result.unionInPlace(piece.output.getAsRelation());
  }
  result.inverse();
  return result;
}

bool DependenceAnalysis::intermediateSources(std::vector<PresburgerRelation>& sinkLevelDeps, unsigned j, unsigned sinkLevel) {
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
      PresburgerRelation T = lastLaterSource(j, level, k, sinkLevel, trest);
      if(T.isIntegerEmpty()) {
        continue;
      }
      // TODO: sinkLevelDeps[j] = sinkLevelDeps[j].intersectRange(trest);
      sinkLevelDeps[k].unionInPlace(T);
    }
  }
}

static PresburgerRelation SymbolicLexOptToPresburgerRelation(const SymbolicLexOpt& s) {
  // TODO
}

// source j
// .
// .
// source k <--- source k writes to same location as source j later
// .
// .
// sink
// TODO: update mustNoSource/mayNoSource instead of passing empty
PresburgerRelation DependenceAnalysis::lastLaterSource(PresburgerRelation curJDeps, int j, int afterLevel, int k, int sinkLevel, PresburgerSet &empty) {
  PresburgerRelation depMap = sink, writeMap = mustSources[k];
  writeMap.inverse();
  depMap.compose(writeMap);// sink -> mustsourceK iterations
  // s.t. sink reads from some location that mustSourceK writes to

  PresburgerSpace space = PresburgerSpace::getRelationSpace(mustSources[k].getNumDomainVars(), mustSources[j].getNumDomainVars());
  // All possible mustSourceK -> sourceJ iterations
  // s.t. mustSourceK iteration is after sourceJ iteration
  PresburgerRelation afterWrite = afterAtLevel(space, afterLevel);
  // All possible mustSourceK -> sink iterations
  // s.t. mustSourceK is after corresponding sourceJ dependence in curJDeps
  afterWrite.compose(curJDeps);
  afterWrite.inverse();
  depMap = depMap.intersect(afterWrite);// sink -> mustSourceK dependencies
  // s.t. sink reads from some location that mustSourceK writes to
  // and mustSourceK is after corresponding sourceJ dependence in curJDeps

  PresburgerRelation beforeSinkRead = afterAtLevel(depMap.getSpace(), sinkLevel);
  depMap = depMap.intersect(beforeSinkRead);// sink -> mustSourceK dependencies
  // s.t. sink reads from some location that mustSourceK writes to
  // and mustSourceK is after corresponding sourceJ dependence in curJDeps
  // and sink read is after SourceK write

  empty = depMap.getDomainSet().subtract(curJDeps.getRangeSet());
  depMap.intersectDomain(curJDeps.getRangeSet());
  SymbolicLexOpt result = depMap.findSymbolicIntegerLexMax();
  return SymbolicLexOptToPresburgerRelation(result);
}

// Return all maySourceJ deps at given level for given sink iterations in set_C
PresburgerRelation DependenceAnalysis::allSources(PresburgerSet& set_C, unsigned j, unsigned level) {
  PresburgerRelation depMap = sink.intersectDomain(set_C), writeMap = maySources[j];
  writeMap.inverse();
  depMap.compose(writeMap);
  PresburgerRelation after = afterAtLevel(depMap.getSpace(), level);
  depMap.intersect(after);
  return depMap;
}

PresburgerRelation DependenceAnalysis::allIntermediateSources(std::vector<PresburgerRelation> mustDeps, std::vector<PresburgerRelation> mayDeps, unsigned j, unsigned sinkLevel) {
}

// must source k
// .
// .
// may source j <--- source j may write to same location as must source k later
// .
// .
// sink
PresburgerRelation DependenceAnalysis::allLaterSources(PresburgerRelation curKDeps, int j, int sinkLevel, int k, int afterLevel) {
  PresburgerRelation depMap = sink.intersectDomain(curKDeps.getRangeSet()), writeMap = maySources[j];
  writeMap.inverse();
  depMap.compose(writeMap);// sink -> maySourceJ iterations
  // s.t. each sink has a RAW dep with some mustSourceK
  // and sink reads from some location that maySourceJ writes to

  PresburgerSpace space = PresburgerSpace::getRelationSpace(maySources[j].getNumDomainVars(), mustSources[k].getNumDomainVars());
  // all possible maySourceJ -> mustSourceK iterations such that maySourceJ is after mustSourceK
  PresburgerRelation afterWrite = afterAtLevel(space, afterLevel);
  // all possible maySourceJ -> sink iterations such that maySourceJ is after
  // corresponding mustSourceK from RAW dep bw sink and mustSourceK
  afterWrite.compose(curKDeps);
  afterWrite.inverse();
  depMap.intersect(afterWrite);// sink -> maySourceJ iterations
  // s.t. each sink has a RAW dep with some mustSourceK
  // and maySourceJ is after mustSourceK from RAW dep bw sink and mustSourceK
  // and there is a RAW dep bw sink and maySourceJ

  // all possible sink -> maySourceJ iterations such that sink is after maySourceJ
  PresburgerRelation beforeRead = afterAtLevel(depMap.getSpace(), sinkLevel);
  depMap.intersect(beforeRead);// sink -> maySourceJ iterations
  // s.t. each sink has a RAW dep with some mustSourceK
  // and maySourceJ is after mustSourceK from RAW dep bw sink and mustSourceK
  // and sink reads from some location that maySourceJ writes to
  // and sink reads after maySourceJ writes
  // i.e. there is a RAW dep bw sink and maySourceJ

  return depMap;
}
