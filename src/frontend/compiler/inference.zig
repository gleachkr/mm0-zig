const Context = @import("./inference/context.zig");
const Diagnostics = @import("./inference/diagnostics.zig");
const Dispatch = @import("./inference/dispatch.zig");
const Strategies = @import("./inference/strategies.zig");
const Validation = @import("./inference/validation.zig");

pub const RuleMatchResult = Strategies.RuleMatchResult;
pub const DepViolationDetail = Validation.DepViolationDetail;
pub const RuleUnifyCache = Context.RuleUnifyCache;
pub const RuleInferenceContext = Context.RuleInferenceContext;
pub const InferenceContext = Context.InferenceContext;
pub const HiddenWitnessFreshContext = Context.HiddenWitnessFreshContext;

pub const validateResolvedBindingsWithDebug =
    Validation.validateResolvedBindingsWithDebug;
pub const validateResolvedBindings = Validation.validateResolvedBindings;
pub const bindingsRespectRuleDeps = Validation.bindingsRespectRuleDeps;
pub const firstDepViolation = Validation.firstDepViolation;
pub const validateBindingExpr = Validation.validateBindingExpr;
pub const exprInfo = Validation.exprInfo;
pub const buildMissingBinderDiagnostic =
    Diagnostics.buildMissingBinderDiagnostic;

pub const canConvertTransparent = Strategies.canConvertTransparent;
pub const inferBindingsTransparent = Strategies.inferBindingsTransparent;
pub const inferBindingsFromRefsOnly = Strategies.inferBindingsFromRefsOnly;
pub const inferBindingsFromHoleyAdvanced =
    Strategies.inferBindingsFromHoleyAdvanced;
pub const inferBindings = Dispatch.inferBindings;
pub const strictInferBindings = Dispatch.strictInferBindings;
pub const hasOmittedBindings = Strategies.hasOmittedBindings;
pub const hasOmittedStructuralBindings =
    Strategies.hasOmittedStructuralBindings;
pub const shouldPreferStructuralSolver =
    Strategies.shouldPreferStructuralSolver;
pub const requireConcreteBindings = Strategies.requireConcreteBindings;
