class SetClass:
    pass

class PosetClass(SetClass):
    pass

class TotalOrderClass(PosetClass):
    pass 
       
class MonoidClass(SetClass):
    pass

class SemiringClass(MonoidClass):
    pass

class OrderedSemiringClass(SemiringClass, TotalOrderClass):
    pass

class SemigroupClass(MonoidClass):
    pass

class GroupClass(SemigroupClass):
    pass

class AbelianGroupClass(GroupClass):
    pass

class RingClass(AbelianGroupClass, SemiringClass):
    pass

class OrderedRingClass(RingClass, TotalOrderClass):
    pass

class FieldClass(RingClass):
    pass

class CompleteFieldClass(FieldClass):
    pass

class ValuedFieldClass(FieldClass):
    pass

class CompleteValuedFieldClass(ValuedFieldClass, CompleteFieldClass):
    pass

class OrderedFieldClass(FieldClass, OrderedRingClass, TotalOrderClass):
    pass

class CompleteOrderedFieldClass(OrderedFieldClass):
    pass

class VectorSpaceClass(AbelianGroupClass):
    pass

class IdealClass(AbelianGroupClass):
    pass

class ModuleClass(AbelianGroupClass):
    pass

class CommutativeModuleClass(ModuleClass):
    pass

class TopologicalSpaceClass(SetClass):
    pass

class MetricSpaceClass(TopologicalSpaceClass):
    pass

class NormedVectorSpaceClass(VectorSpaceClass, MetricSpaceClass):
    pass

class InnerProductSpaceClass(NormedVectorSpaceClass):
    pass

class BanachSpaceClass(NormedVectorSpaceClass):
    pass

class HilbertSpaceClass(BanachSpaceClass, InnerProductSpaceClass):
    pass

class HausdorffTopologicalSpaceClass(TopologicalSpaceClass):
    pass

class TopologicalGroupClass(GroupClass, TopologicalSpaceClass):
    pass

class FunctionClass(SetClass):
    pass