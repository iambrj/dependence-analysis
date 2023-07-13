#include <mlir/Analysis/Presburger/IntegerRelation.h>
#include <mlir/Analysis/Presburger/PresburgerSpace.h>
#include <mlir/Analysis/Presburger/PresburgerRelation.h>

#include <llvm/ADT/ArrayRef.h>

#include <iostream>

using namespace mlir::presburger;
using namespace llvm;
using namespace std;

PresburgerRelation compose(PresburgerRelation r1, PresburgerRelation r2) {
  PresburgerRelation result = PresburgerRelation::getEmpty(PresburgerSpace::getRelationSpace(r1.getNumDomainVars(), r2.getNumRangeVars(), r1.getNumSymbolVars()));
  for (const IntegerRelation &csA : r1.getAllDisjuncts()) {
    for (const IntegerRelation &csB : r2.getAllDisjuncts()) {
      IntegerRelation composition = csA;
      composition.compose(csB);
      if (!composition.isEmpty())
        result.unionInPlace(composition);
    }
  }
  return result;
}

int main() {
  PresburgerSpace s1 = PresburgerSpace::getRelationSpace(2, 2, 1, 0), s2 = PresburgerSpace::getRelationSpace(2, 1, 1, 0);
  IntegerRelation IR1 = IntegerRelation::getUniverse(s1), IR2 =
    IntegerRelation::getUniverse(s1), IR3 = IntegerRelation::getUniverse(s1),
    IRa = IntegerRelation::getUniverse(s2), IRb =
      IntegerRelation::getUniverse(s2), IRc = IntegerRelation::getUniverse(s2);
  vector<MPInt>  veq11 = {MPInt(1), MPInt(0), MPInt(-1), MPInt(0), MPInt(1), MPInt(0)}
               , veq12 = {MPInt(0), MPInt(1), MPInt(0), MPInt(-1), MPInt(-1), MPInt(0)}
               , veq21 = {MPInt(1), MPInt(0), MPInt(0), MPInt(-1), MPInt(0), MPInt(0)}
               , veq22 = {MPInt(0), MPInt(1), MPInt(-1), MPInt(0), MPInt(0), MPInt(0)}
               , veq31 = {MPInt(1), MPInt(1), MPInt(-1), MPInt(0), MPInt(0), MPInt(0)}
               , veq32 = {MPInt(-1), MPInt(1), MPInt(0), MPInt(1), MPInt(0), MPInt(0)}
               , veqa = {MPInt(1), MPInt(1), MPInt(-1), MPInt(0), MPInt(0)}
               , veqb = {MPInt(0), MPInt(0), MPInt(1), MPInt(-1), MPInt(0)}
               , veqc = {MPInt(1), MPInt(-1), MPInt(1), MPInt(0), MPInt(0)};
  ArrayRef<MPInt> eq11(veq11)
               , eq12(veq12)
               , eq21(veq21)
               , eq22(veq22)
               , eq31(veq31)
               , eq32(veq32)
               , eqa (veqa)
               , eqb (veqb)
               , eqc (veqc);
  IR1.addEquality(eq11);
  IR1.addEquality(eq12);
  IR2.addEquality(eq21);
  IR2.addEquality(eq22);
  IR3.addEquality(eq31);
  IR3.addEquality(eq32);
  IRa.addEquality(eqa);
  IRb.addEquality(eqb);
  IRc.addEquality(eqc);
  PresburgerRelation PR1(IR1), PR2(IRa);
  PR1.unionInPlace(IR2);
  PR1.unionInPlace(IR3);
  PR2.unionInPlace(IRb);
  PR2.unionInPlace(IRc);
  PresburgerRelation comp = compose(PR1, PR2);
  IntegerRelation IR1a = IntegerRelation::getUniverse(s2)
                , IR1b = IntegerRelation::getUniverse(s2)
                , IR1c = IntegerRelation::getUniverse(s2)
                , IR2a = IntegerRelation::getUniverse(s2)
                , IR2b = IntegerRelation::getUniverse(s2)
                , IR2c = IntegerRelation::getUniverse(s2)
                , IR3a = IntegerRelation::getUniverse(s2)
                , IR3b = IntegerRelation::getUniverse(s2)
                , IR3c = IntegerRelation::getUniverse(s2);
  vector<MPInt>  veq1a = {MPInt(1), MPInt(1), MPInt(-1), MPInt(0), MPInt(0)}
               , veq1b = {MPInt(0), MPInt(0), MPInt(1), MPInt(-1), MPInt(0)}
               , veq1c = {MPInt(1), MPInt(-1), MPInt(1), MPInt(2), MPInt(0)}
               , veq2a = {MPInt(1), MPInt(1), MPInt(-1), MPInt(0), MPInt(0)}
               , veq2b = {MPInt(0), MPInt(0), MPInt(1), MPInt(-1), MPInt(0)}
               , veq2c = {MPInt(-1), MPInt(1), MPInt(1), MPInt(0), MPInt(0)}
               , veq3a = {MPInt(-2), MPInt(0), MPInt(1), MPInt(0), MPInt(0)}
               , veq3b = {MPInt(0), MPInt(0), MPInt(1), MPInt(-1), MPInt(0)}
               , veq3c = {MPInt(0), MPInt(2), MPInt(1), MPInt(0), MPInt(0)};
  ArrayRef<MPInt>  eq1a(veq1a)
                 , eq1b(veq1b)
                 , eq1c(veq1c)
                 , eq2a(veq2a)
                 , eq2b(veq2b)
                 , eq2c(veq2c)
                 , eq3a(veq3a)
                 , eq3b(veq3b)
                 , eq3c(veq3c);
  IR1a.addEquality(eq1a);
  IR1b.addEquality(eq1b);
  IR1c.addEquality(eq1c);
  IR2a.addEquality(eq2a);
  IR2b.addEquality(eq2b);
  IR2c.addEquality(eq2c);
  IR3a.addEquality(eq3a);
  IR3b.addEquality(eq3b);
  IR3c.addEquality(eq3c);
  PresburgerRelation expected(IR1a);
        expected.unionInPlace(IR1b);
        expected.unionInPlace(IR1c);
        expected.unionInPlace(IR2a);
        expected.unionInPlace(IR2b);
        expected.unionInPlace(IR2c);
        expected.unionInPlace(IR3a);
        expected.unionInPlace(IR3b);
        expected.unionInPlace(IR3c);
  cout << expected.isEqual(comp) << endl;

}
