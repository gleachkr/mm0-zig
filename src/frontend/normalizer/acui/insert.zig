const ExprId = @import("../../compiler_expr.zig").ExprId;
const AcuiSupport = @import("../../acui_support.zig");
const compareExprIds = AcuiSupport.compareExprIds;
const ResolvedRelation = @import("../../rewrite_registry.zig").ResolvedRelation;
const ResolvedStructuralCombiner =
    @import("../../rewrite_registry.zig").ResolvedStructuralCombiner;
const ProofEmit = @import("../proof_emit.zig");
const Types = @import("../types.zig");

const NormalizeResult = Types.NormalizeResult;

pub fn insertItem(
    self: anytype,
    current_expr: ExprId,
    item: ExprId,
    canon: ExprId,
    relation: ResolvedRelation,
    acui: ResolvedStructuralCombiner,
) anyerror!NormalizeResult {
    const unit_expr = try ProofEmit.unitExpr(self, acui);
    if (item == unit_expr) {
        return .{
            .result_expr = canon,
            .conv_line_idx = try ProofEmit.emitLeftUnit(
                self,
                current_expr,
                canon,
                relation,
                acui,
            ),
        };
    }
    if (canon == unit_expr) {
        return .{
            .result_expr = item,
            .conv_line_idx = try ProofEmit.emitRightUnit(
                self,
                item,
                relation,
                acui,
            ),
        };
    }

    const canon_node = self.theorem.interner.node(canon);
    switch (canon_node.*) {
        .variable => {
            return try insertIntoAtom(
                self,
                current_expr,
                item,
                canon,
                relation,
                acui,
            );
        },
        .app => |canon_app| {
            if (canon_app.term_id != acui.head_term_id or
                canon_app.args.len != 2)
            {
                return try insertIntoAtom(
                    self,
                    current_expr,
                    item,
                    canon,
                    relation,
                    acui,
                );
            }

            const head = canon_app.args[0];
            const rest = canon_app.args[1];
            const cmp = compareExprIds(self.theorem, item, head);
            if (cmp == .eq and acui.idem_id != null) {
                const assoc_sym_idx = try ProofEmit.emitAssocSymm(
                    self,
                    item,
                    head,
                    rest,
                    relation,
                    acui,
                );
                const inner_old = try self.theorem.interner.internApp(
                    acui.head_term_id,
                    &[_]ExprId{ item, head },
                );
                const idem_idx = try ProofEmit.emitIdem(
                    self,
                    item,
                    relation,
                    acui,
                );
                const lifted = try ProofEmit.emitCongruenceLine(
                    self,
                    acui.head_term_id,
                    &[_]ExprId{ inner_old, rest },
                    &[_]ExprId{ item, rest },
                    &[_]?usize{ idem_idx, null },
                );
                const proof = try ProofEmit.composeTransitivity(
                    self,
                    relation,
                    current_expr,
                    try switchAssoc(self, item, head, rest, acui),
                    canon,
                    assoc_sym_idx,
                    lifted,
                );
                return .{
                    .result_expr = canon,
                    .conv_line_idx = proof,
                };
            }
            if (cmp != .gt or acui.comm_id == null) {
                return .{
                    .result_expr = current_expr,
                    .conv_line_idx = null,
                };
            }

            const assoc_sym_target = try switchAssoc(
                self,
                item,
                head,
                rest,
                acui,
            );
            const assoc_sym_idx = try ProofEmit.emitAssocSymm(
                self,
                item,
                head,
                rest,
                relation,
                acui,
            );
            const inner_old = try self.theorem.interner.internApp(
                acui.head_term_id,
                &[_]ExprId{ item, head },
            );
            const inner_new = try self.theorem.interner.internApp(
                acui.head_term_id,
                &[_]ExprId{ head, item },
            );
            const comm_idx = try ProofEmit.emitComm(
                self,
                item,
                head,
                relation,
                acui,
            );
            const lifted_comm = try ProofEmit.emitCongruenceLine(
                self,
                acui.head_term_id,
                &[_]ExprId{ inner_old, rest },
                &[_]ExprId{ inner_new, rest },
                &[_]?usize{ comm_idx, null },
            );
            const assoc_idx = try ProofEmit.emitAssoc(
                self,
                head,
                item,
                rest,
                relation,
                acui,
            );
            const before_rec = try self.theorem.interner.internApp(
                acui.head_term_id,
                &[_]ExprId{ item, rest },
            );
            const rec = try insertItem(
                self,
                before_rec,
                item,
                rest,
                relation,
                acui,
            );
            const lifted_rec = if (rec.conv_line_idx) |rec_idx|
                try ProofEmit.emitCongruenceLine(
                    self,
                    acui.head_term_id,
                    &[_]ExprId{ head, before_rec },
                    &[_]ExprId{ head, rec.result_expr },
                    &[_]?usize{ null, rec_idx },
                )
            else
                null;
            const first = try ProofEmit.composeTransitivity(
                self,
                relation,
                current_expr,
                assoc_sym_target,
                try self.theorem.interner.internApp(
                    acui.head_term_id,
                    &[_]ExprId{ inner_new, rest },
                ),
                assoc_sym_idx,
                lifted_comm,
            );
            const second = try ProofEmit.composeTransitivity(
                self,
                relation,
                current_expr,
                try self.theorem.interner.internApp(
                    acui.head_term_id,
                    &[_]ExprId{ inner_new, rest },
                ),
                try self.theorem.interner.internApp(
                    acui.head_term_id,
                    &[_]ExprId{ head, before_rec },
                ),
                first,
                assoc_idx,
            );
            const proof = try ProofEmit.composeTransitivity(
                self,
                relation,
                current_expr,
                try self.theorem.interner.internApp(
                    acui.head_term_id,
                    &[_]ExprId{ head, before_rec },
                ),
                try self.theorem.interner.internApp(
                    acui.head_term_id,
                    &[_]ExprId{ head, rec.result_expr },
                ),
                second,
                lifted_rec,
            );
            return .{
                .result_expr = if (rec.result_expr == before_rec)
                    try self.theorem.interner.internApp(
                        acui.head_term_id,
                        &[_]ExprId{ head, before_rec },
                    )
                else
                    try self.theorem.interner.internApp(
                        acui.head_term_id,
                        &[_]ExprId{ head, rec.result_expr },
                    ),
                .conv_line_idx = proof,
            };
        },
    }
}

pub fn insertIntoAtom(
    self: anytype,
    current_expr: ExprId,
    item: ExprId,
    atom: ExprId,
    relation: ResolvedRelation,
    acui: ResolvedStructuralCombiner,
) anyerror!NormalizeResult {
    const cmp = compareExprIds(self.theorem, item, atom);
    if (cmp == .eq and acui.idem_id != null) {
        return .{
            .result_expr = atom,
            .conv_line_idx = try ProofEmit.emitIdem(
                self,
                item,
                relation,
                acui,
            ),
        };
    }
    if (cmp != .gt or acui.comm_id == null) {
        return .{
            .result_expr = current_expr,
            .conv_line_idx = null,
        };
    }
    return .{
        .result_expr = try self.theorem.interner.internApp(
            acui.head_term_id,
            &[_]ExprId{ atom, item },
        ),
        .conv_line_idx = try ProofEmit.emitComm(
            self,
            item,
            atom,
            relation,
            acui,
        ),
    };
}

pub fn switchAssoc(
    self: anytype,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    acui: ResolvedStructuralCombiner,
) anyerror!ExprId {
    return try self.theorem.interner.internApp(
        acui.head_term_id,
        &[_]ExprId{
            try self.theorem.interner.internApp(
                acui.head_term_id,
                &[_]ExprId{ a, b },
            ),
            c,
        },
    );
}
