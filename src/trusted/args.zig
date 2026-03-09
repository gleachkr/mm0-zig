pub const Arg = packed struct {
    /// bit i set means depends on ith bound variable
    deps: u55,
    /// must be 0
    reserved: u1,
    /// index into the sort table
    sort: u7,
    /// is it a bound variable
    bound: bool,

    pub fn dependsOn(self: Arg, bv_index: u6) bool {
        return (self.deps >> bv_index) & 1 != 0;
    }

    pub fn depsOverlap(self: Arg, other_deps: u55) bool {
        return (self.deps & other_deps) != 0;
    }
};
