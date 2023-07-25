class SetClass:
    pass

class PosetClass(SetClass):
    pass

class TotalOrderClass(PosetClass):
    pass 
       
class MonoidClass(SetClass):
    pass

class SemigroupClass(MonoidClass):
    pass

class GroupClass(SemigroupClass):
    pass

class AbelianGroupClass(GroupClass):
    pass

class RingClass(AbelianGroupClass):
    pass

class FieldClass(RingClass):
    pass

class OrderedFieldClass(FieldClass, TotalOrderClass):
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

