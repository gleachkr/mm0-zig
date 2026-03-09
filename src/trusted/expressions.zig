pub const Expr = union(enum) {
    variable: Variable,
    term: TermApp,

    pub fn sort(self: *const Expr) u7 {
        return switch (self.*) {
            .variable => |v| v.sort,
            .term => |t| t.sort,
        };
    }

    pub fn deps(self: *const Expr) u55 {
        return switch (self.*) {
            .variable => |v| v.deps,
            .term => |t| t.deps,
        };
    }

    pub fn bound(self: *const Expr) bool {
        return switch (self.*) {
            .variable => |v| v.bound,
            .term => false,
        };
    }
};

pub const Variable = struct {
    /// index into sort table
    sort: u7,
    /// is it bound
    bound: bool,
    // if bound: 1 << own_index, if regular, a bitmask for the declared dependencies
    deps: u55,
};

pub const TermApp = struct {
    //// index into sort table
    sort: u7,
    /// we cache the deps of the children here
    deps: u55,
    id: u32,
    /// pointers into the arena
    args: []const *const Expr,
};
