const SharedContext = @import("./shared_context.zig").SharedContext;
const TransparentMatch =
    @import("./symbolic_engine/transparent_match.zig");
const SemanticSearch =
    @import("./symbolic_engine/semantic_search.zig");
const RewriteApplication =
    @import("./symbolic_engine/rewrite_application.zig");
const WitnessState = @import("./symbolic_engine/witness_state.zig");

const SymbolicExpr = @import("./types.zig").SymbolicExpr;

pub const SemanticStepCandidate = SemanticSearch.SemanticStepCandidate;

pub const SymbolicEngine = struct {
    shared: *SharedContext,

    pub const defCoversItem = TransparentMatch.defCoversItem;
    pub const planDefCoversItem = TransparentMatch.planDefCoversItem;
    pub const instantiateDefTowardAcuiItem =
        TransparentMatch.instantiateDefTowardAcuiItem;
    pub const planDefToTarget = TransparentMatch.planDefToTarget;
    pub const compareTransparent = TransparentMatch.compareTransparent;
    pub const matchTemplateTransparent =
        TransparentMatch.matchTemplateTransparent;
    pub const instantiateDefTowardExpr =
        TransparentMatch.instantiateDefTowardExpr;
    pub const matchTemplateRecState =
        TransparentMatch.matchTemplateRecState;
    pub const matchTemplateSemantic = SemanticSearch.matchTemplateSemantic;
    pub const collectSemanticStepCandidatesExpr =
        SemanticSearch.collectSemanticStepCandidatesExpr;
    pub const collectSemanticStepCandidatesSymbolic =
        SemanticSearch.collectSemanticStepCandidatesSymbolic;
    pub const matchTemplateSemanticState =
        SemanticSearch.matchTemplateSemanticState;
    pub const matchSymbolicToExprSemantic =
        SemanticSearch.matchSymbolicToExprSemantic;
    pub const matchSymbolicToSymbolicSemantic =
        SemanticSearch.matchSymbolicToSymbolicSemantic;
    pub const matchSymbolicAcuiLeafToExprSemantic =
        SemanticSearch.matchSymbolicAcuiLeafToExprSemantic;
    pub const applyRewriteRuleToExpr =
        RewriteApplication.applyRewriteRuleToExpr;
    pub const applyRewriteRuleToSymbolic =
        RewriteApplication.applyRewriteRuleToSymbolic;

    pub const boundValueFromSeed = WitnessState.boundValueFromSeed;
    pub const chooseRepresentative = WitnessState.chooseRepresentative;
    pub const chooseRepresentativeSymbolic =
        WitnessState.chooseRepresentativeSymbolic;
    pub const symbolicExprEql = WitnessState.symbolicExprEql;
    pub const assignBinderValue = WitnessState.assignBinderValue;
    pub const finalizeBoundValue = WitnessState.finalizeBoundValue;
    pub const concreteBindingMatchExpr =
        WitnessState.concreteBindingMatchExpr;
    pub const materializeResolvedBoundValue =
        WitnessState.materializeResolvedBoundValue;
    pub const projectMaterializedExpr =
        WitnessState.projectMaterializedExpr;
    pub const collectUnresolvedRootsInBoundValue =
        WitnessState.collectUnresolvedRootsInBoundValue;
    pub const collectConcreteDepsInBoundValue =
        WitnessState.collectConcreteDepsInBoundValue;
    pub const resolveDummySlot = WitnessState.resolveDummySlot;
    pub const currentWitnessExpr = WitnessState.currentWitnessExpr;
    pub const isProvisionalWitnessExpr =
        WitnessState.isProvisionalWitnessExpr;
    pub const makeConcreteBoundValue =
        WitnessState.makeConcreteBoundValue;
    pub const makeSymbolicBoundValue =
        WitnessState.makeSymbolicBoundValue;
    pub const concreteExprsMatchMode =
        WitnessState.concreteExprsMatchMode;
    pub const invalidateRepresentativeCaches =
        WitnessState.invalidateRepresentativeCaches;
    pub const matchSymbolicDummyState =
        WitnessState.matchSymbolicDummyState;
    pub const matchDummyToSymbolic = WitnessState.matchDummyToSymbolic;

    pub fn allocSymbolic(
        self: *SymbolicEngine,
        symbolic: SymbolicExpr,
    ) anyerror!*const SymbolicExpr {
        const node = try self.shared.allocator.create(SymbolicExpr);
        node.* = symbolic;
        return node;
    }
};
