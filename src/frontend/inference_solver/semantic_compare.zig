const ExprId = @import("../expr.zig").ExprId;

pub fn commonStructuralTarget(
    self: anytype,
    lhs: ExprId,
    rhs: ExprId,
) anyerror!?ExprId {
    var support = self.structuralSupport();
    return try support.buildCommonTarget(lhs, rhs);
}

pub fn bindingCompatible(
    self: anytype,
    lhs: ExprId,
    rhs: ExprId,
) anyerror!bool {
    if (lhs == rhs) return true;
    const lhs_canon = try self.canonicalizer.canonicalize(lhs);
    const rhs_canon = try self.canonicalizer.canonicalize(rhs);
    if (lhs_canon == rhs_canon) return true;
    return (try commonStructuralTarget(self, lhs_canon, rhs_canon)) != null;
}

pub fn sameRuleBindingsCompatible(
    self: anytype,
    lhs: []const ?ExprId,
    rhs: []const ?ExprId,
) anyerror!bool {
    return try sameBindingsCompatible(self, lhs, rhs);
}

pub fn sameBindingsCompatible(
    self: anytype,
    lhs: []const ?ExprId,
    rhs: []const ?ExprId,
) anyerror!bool {
    if (lhs.len != rhs.len) return false;
    for (lhs, rhs) |l, r| {
        if (l == null or r == null) {
            if (l != r) return false;
            continue;
        }
        if (!try bindingCompatible(self, l.?, r.?)) return false;
    }
    return true;
}
