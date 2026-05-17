const BoundValue = @import("bound_value.zig");
const Representative = @import("representative.zig");
const SymbolicExpr = @import("symbolic_expr.zig");
const DummySlots = @import("dummy_slots.zig");
const MatchSnapshot = @import("match_snapshot.zig");
const BoundValueMatch = @import("bound_value_match.zig");
const Materialize = @import("materialize.zig");

pub const rebuildBoundValue = BoundValue.rebuildBoundValue;
pub const rebuildBoundValueFromState = BoundValue.rebuildBoundValueFromState;
pub const makeConcreteBoundValue = BoundValue.makeConcreteBoundValue;
pub const makeSymbolicBoundValue = BoundValue.makeSymbolicBoundValue;
pub const invalidateRepresentativeCaches =
    BoundValue.invalidateRepresentativeCaches;
pub const assignBinderFromExpr = BoundValue.assignBinderFromExpr;
pub const assignBinderFromSymbolic = BoundValue.assignBinderFromSymbolic;
pub const assignBinderValue = BoundValue.assignBinderValue;
pub const boundValueFromSeed = BoundValue.boundValueFromSeed;
pub const chooseRepresentative = Representative.chooseRepresentative;
pub const representativeCacheForMode =
    Representative.representativeCacheForMode;
pub const chooseRepresentativeSymbolic =
    Representative.chooseRepresentativeSymbolic;
pub const rebuildExprRepresentativeSymbolic =
    Representative.rebuildExprRepresentativeSymbolic;
pub const compressRepresentativeToDef = Representative.compressRepresentativeToDef;
pub const resymbolizePlaceholderExpr =
    Representative.resymbolizePlaceholderExpr;
pub const symbolicSortName = SymbolicExpr.symbolicSortName;
pub const symbolicToConcreteIfPlain = SymbolicExpr.symbolicToConcreteIfPlain;
pub const symbolicExprEql = SymbolicExpr.symbolicExprEql;
pub const boundValueRepresentative = SymbolicExpr.boundValueRepresentative;
pub const exprSortName = SymbolicExpr.exprSortName;
pub const resymbolizeBinding = SymbolicExpr.resymbolizeBinding;
pub const symbolicForExistingConcreteBinding =
    SymbolicExpr.symbolicForExistingConcreteBinding;
pub const slotForWitness = DummySlots.slotForWitness;
pub const resolveDummySlot = DummySlots.resolveDummySlot;
pub const putWitnessForDummySlot = DummySlots.putWitnessForDummySlot;
pub const alignDummySlots = DummySlots.alignDummySlots;
pub const saveMatchSnapshot = MatchSnapshot.saveMatchSnapshot;
pub const restoreMatchSnapshot = MatchSnapshot.restoreMatchSnapshot;
pub const deinitMatchSnapshot = MatchSnapshot.deinitMatchSnapshot;
pub const cloneWitnessMap = MatchSnapshot.cloneWitnessMap;
pub const cloneWitnessSlotMap = MatchSnapshot.cloneWitnessSlotMap;
pub const cloneDummyAliasMap = MatchSnapshot.cloneDummyAliasMap;
pub const cloneProvisionalWitnessInfoMap =
    MatchSnapshot.cloneProvisionalWitnessInfoMap;
pub const cloneMaterializedWitnessInfoMap =
    MatchSnapshot.cloneMaterializedWitnessInfoMap;
pub const cloneRepresentativeCache = MatchSnapshot.cloneRepresentativeCache;
pub const cloneRepresentativeState = MatchSnapshot.cloneRepresentativeState;
pub const boundValueMatchesExpr = BoundValueMatch.boundValueMatchesExpr;
pub const concreteExprsMatchMode = BoundValueMatch.concreteExprsMatchMode;
pub const concreteBindingMatchesExpr = BoundValueMatch.concreteBindingMatchesExpr;
pub const boundValueMatchesSymbolic =
    BoundValueMatch.boundValueMatchesSymbolic;
pub const concreteBindingMatchExpr = BoundValueMatch.concreteBindingMatchExpr;
pub const matchSymbolicDummyState = BoundValueMatch.matchSymbolicDummyState;
pub const matchDummyToSymbolic = BoundValueMatch.matchDummyToSymbolic;
pub const representResolvedBindings = Materialize.representResolvedBindings;
pub const collectUnresolvedRootsInBoundValue =
    Materialize.collectUnresolvedRootsInBoundValue;
pub const collectConcreteDepsInBoundValue =
    Materialize.collectConcreteDepsInBoundValue;
pub const materializeResolvedBoundValue =
    Materialize.materializeResolvedBoundValue;
pub const projectMaterializedExpr = Materialize.projectMaterializedExpr;
pub const finalizeBoundValue = Materialize.finalizeBoundValue;
pub const materializeAssignedBoundValue =
    Materialize.materializeAssignedBoundValue;
pub const materializeRepresentativeSymbolic =
    Materialize.materializeRepresentativeSymbolic;
pub const materializeAssignedSymbolic = Materialize.materializeAssignedSymbolic;
pub const materializeResolvedSymbolic = Materialize.materializeResolvedSymbolic;
pub const materializeFinalSymbolic = Materialize.materializeFinalSymbolic;
pub const currentWitnessExpr = Materialize.currentWitnessExpr;
pub const isProvisionalWitnessExpr = Materialize.isProvisionalWitnessExpr;
pub const resolveWitnessForDummySlot =
    Materialize.resolveWitnessForDummySlot;
pub const getConcreteLeafInfo = Materialize.getConcreteLeafInfo;
