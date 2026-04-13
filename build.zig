const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});
    const lsp_dep = b.dependency("lsp_kit", .{});
    const lsp_module = lsp_dep.module("lsp");

    const mm0_lib = b.createModule(.{
        .root_source_file = b.path("src/lib.zig"),
        .target = target,
        .optimize = optimize,
    });

    const wasm_target = b.resolveTargetQuery(.{
        .cpu_arch = .wasm32,
        .os_tag = .freestanding,
    });
    const mm0_wasm_lib = b.createModule(.{
        .root_source_file = b.path("src/lib.zig"),
        .target = wasm_target,
        .optimize = optimize,
    });

    const verifier_module = b.createModule(.{
        .root_source_file = b.path("src/bin/verifier/main.zig"),
        .target = target,
        .optimize = optimize,
    });
    verifier_module.addImport("mm0", mm0_lib);

    const verifier_exe = b.addExecutable(.{
        .name = "mm0-zig",
        .root_module = verifier_module,
    });
    b.installArtifact(verifier_exe);

    const compiler_module = b.createModule(.{
        .root_source_file = b.path("src/bin/compiler/main.zig"),
        .target = target,
        .optimize = optimize,
    });
    compiler_module.addImport("mm0", mm0_lib);
    compiler_module.addImport("lsp", lsp_module);

    const compiler_exe = b.addExecutable(.{
        .name = "abc",
        .root_module = compiler_module,
    });
    b.installArtifact(compiler_exe);

    const compiler_wasm_module = b.createModule(.{
        .root_source_file = b.path("src/bin/compiler/wasm.zig"),
        .target = wasm_target,
        .optimize = optimize,
    });
    compiler_wasm_module.addImport("mm0", mm0_wasm_lib);

    const compiler_wasm = b.addExecutable(.{
        .name = "abc-web",
        .root_module = compiler_wasm_module,
    });
    compiler_wasm.entry = .disabled;
    compiler_wasm.rdynamic = true;
    compiler_wasm.export_memory = true;

    const verifier_wasm_module = b.createModule(.{
        .root_source_file = b.path("src/bin/verifier/wasm.zig"),
        .target = wasm_target,
        .optimize = optimize,
    });
    verifier_wasm_module.addImport("mm0", mm0_wasm_lib);

    const verifier_wasm = b.addExecutable(.{
        .name = "mm0-zig-web",
        .root_module = verifier_wasm_module,
    });
    verifier_wasm.entry = .disabled;
    verifier_wasm.rdynamic = true;
    verifier_wasm.export_memory = true;

    const web_demo_step = b.step("web-demo", "Build the browser demo");
    const install_compiler_wasm = b.addInstallArtifact(compiler_wasm, .{
        .dest_dir = .{ .override = .prefix },
        .dest_sub_path = "web-demo/compiler.wasm",
    });
    const install_verifier_wasm = b.addInstallArtifact(verifier_wasm, .{
        .dest_dir = .{ .override = .prefix },
        .dest_sub_path = "web-demo/verifier.wasm",
    });
    const install_web_assets = b.addInstallDirectory(.{
        .source_dir = b.path("web"),
        .install_dir = .prefix,
        .install_subdir = "web-demo",
    });
    const install_web_fonts = b.addInstallDirectory(.{
        .source_dir = b.path("web/fonts"),
        .install_dir = .prefix,
        .install_subdir = "web-demo/fonts",
    });
    const install_hilbert_mm0 = b.addInstallFile(
        b.path("tests/proof_cases/hilbert.mm0"),
        "web-demo/fixtures/hilbert.mm0",
    );
    const install_hilbert_proof = b.addInstallFile(
        b.path("tests/proof_cases/hilbert.auf"),
        "web-demo/fixtures/hilbert.auf",
    );
    const install_hilbert_russell_mm0 = b.addInstallFile(
        b.path("tests/proof_cases/hilbert_russell.mm0"),
        "web-demo/fixtures/hilbert_russell.mm0",
    );
    const install_hilbert_russell_proof = b.addInstallFile(
        b.path("tests/proof_cases/hilbert_russell.auf"),
        "web-demo/fixtures/hilbert_russell.auf",
    );
    const install_prop_cnf_mm0 = b.addInstallFile(
        b.path("tests/proof_cases/demo_prop_cnf.mm0"),
        "web-demo/fixtures/demo_prop_cnf.mm0",
    );
    const install_prop_cnf_proof = b.addInstallFile(
        b.path("tests/proof_cases/demo_prop_cnf.auf"),
        "web-demo/fixtures/demo_prop_cnf.auf",
    );
    const install_nd_em_mm0 = b.addInstallFile(
        b.path("tests/proof_cases/demo_nd_excluded_middle.mm0"),
        "web-demo/fixtures/demo_nd_excluded_middle.mm0",
    );
    const install_nd_em_proof = b.addInstallFile(
        b.path("tests/proof_cases/demo_nd_excluded_middle.auf"),
        "web-demo/fixtures/demo_nd_excluded_middle.auf",
    );
    const install_seq_peirce_mm0 = b.addInstallFile(
        b.path("tests/proof_cases/demo_seq_peirce.mm0"),
        "web-demo/fixtures/demo_seq_peirce.mm0",
    );
    const install_seq_peirce_proof = b.addInstallFile(
        b.path("tests/proof_cases/demo_seq_peirce.auf"),
        "web-demo/fixtures/demo_seq_peirce.auf",
    );
    const install_lk_exists_mono_mm0 = b.addInstallFile(
        b.path("tests/proof_cases/demo_lk_exists_mono.mm0"),
        "web-demo/fixtures/demo_lk_exists_mono.mm0",
    );
    const install_lk_exists_mono_proof = b.addInstallFile(
        b.path("tests/proof_cases/demo_lk_exists_mono.auf"),
        "web-demo/fixtures/demo_lk_exists_mono.auf",
    );
    const install_quant_nd_mm0 = b.addInstallFile(
        b.path("tests/proof_cases/quant_nd.mm0"),
        "web-demo/fixtures/quant_nd.mm0",
    );
    const install_quant_nd_proof = b.addInstallFile(
        b.path("tests/proof_cases/quant_nd.auf"),
        "web-demo/fixtures/quant_nd.auf",
    );
    const install_hol_beta_mm0 = b.addInstallFile(
        b.path("tests/proof_cases/demo_hol_beta.mm0"),
        "web-demo/fixtures/demo_hol_beta.mm0",
    );
    const install_hol_beta_proof = b.addInstallFile(
        b.path("tests/proof_cases/demo_hol_beta.auf"),
        "web-demo/fixtures/demo_hol_beta.auf",
    );
    const install_calculus_product_rule_mm0 = b.addInstallFile(
        b.path("tests/proof_cases/demo_calculus_product_rule.mm0"),
        "web-demo/fixtures/demo_calculus_product_rule.mm0",
    );
    const install_calculus_product_rule_proof = b.addInstallFile(
        b.path("tests/proof_cases/demo_calculus_product_rule.auf"),
        "web-demo/fixtures/demo_calculus_product_rule.auf",
    );
    const install_category_pullback_mm0 = b.addInstallFile(
        b.path("tests/proof_cases/demo_category_pullback.mm0"),
        "web-demo/fixtures/demo_category_pullback.mm0",
    );
    const install_category_pullback_proof = b.addInstallFile(
        b.path("tests/proof_cases/demo_category_pullback.auf"),
        "web-demo/fixtures/demo_category_pullback.auf",
    );
    web_demo_step.dependOn(&install_compiler_wasm.step);
    web_demo_step.dependOn(&install_verifier_wasm.step);
    web_demo_step.dependOn(&install_web_assets.step);
    web_demo_step.dependOn(&install_web_fonts.step);
    web_demo_step.dependOn(&install_hilbert_mm0.step);
    web_demo_step.dependOn(&install_hilbert_proof.step);
    web_demo_step.dependOn(&install_hilbert_russell_mm0.step);
    web_demo_step.dependOn(&install_hilbert_russell_proof.step);
    web_demo_step.dependOn(&install_prop_cnf_mm0.step);
    web_demo_step.dependOn(&install_prop_cnf_proof.step);
    web_demo_step.dependOn(&install_nd_em_mm0.step);
    web_demo_step.dependOn(&install_nd_em_proof.step);
    web_demo_step.dependOn(&install_seq_peirce_mm0.step);
    web_demo_step.dependOn(&install_seq_peirce_proof.step);
    web_demo_step.dependOn(&install_lk_exists_mono_mm0.step);
    web_demo_step.dependOn(&install_lk_exists_mono_proof.step);
    web_demo_step.dependOn(&install_quant_nd_mm0.step);
    web_demo_step.dependOn(&install_quant_nd_proof.step);
    web_demo_step.dependOn(&install_hol_beta_mm0.step);
    web_demo_step.dependOn(&install_hol_beta_proof.step);
    web_demo_step.dependOn(&install_calculus_product_rule_mm0.step);
    web_demo_step.dependOn(&install_calculus_product_rule_proof.step);
    web_demo_step.dependOn(&install_category_pullback_mm0.step);
    web_demo_step.dependOn(&install_category_pullback_proof.step);

    const run_step = b.step("run", "Run the mm0-zig verifier");
    const run_cmd = b.addRunArtifact(verifier_exe);
    run_step.dependOn(&run_cmd.step);
    run_cmd.step.dependOn(b.getInstallStep());

    const run_compiler_step = b.step(
        "run-compiler",
        "Run the abc compiler",
    );
    const run_compiler_cmd = b.addRunArtifact(compiler_exe);
    run_compiler_step.dependOn(&run_compiler_cmd.step);
    run_compiler_cmd.step.dependOn(b.getInstallStep());

    if (b.args) |args| {
        run_cmd.addArgs(args);
        run_compiler_cmd.addArgs(args);
    }

    const trusted_test_module = b.createModule(.{
        .root_source_file = b.path("src/trusted/tests.zig"),
        .target = target,
        .optimize = optimize,
    });
    trusted_test_module.addImport("mm0", mm0_lib);

    const trusted_tests = b.addTest(.{
        .root_module = trusted_test_module,
    });
    const run_trusted_tests = b.addRunArtifact(trusted_tests);

    const root_test_module = b.createModule(.{
        .root_source_file = b.path("src/tests.zig"),
        .target = target,
        .optimize = optimize,
    });
    root_test_module.addImport("mm0", mm0_lib);

    const root_tests = b.addTest(.{
        .root_module = root_test_module,
    });
    const run_root_tests = b.addRunArtifact(root_tests);

    const frontend_test_module = b.createModule(.{
        .root_source_file = b.path("src/frontend/tests.zig"),
        .target = target,
        .optimize = optimize,
    });
    frontend_test_module.addImport("mm0", mm0_lib);

    const frontend_tests = b.addTest(.{
        .root_module = frontend_test_module,
    });
    const run_frontend_tests = b.addRunArtifact(frontend_tests);

    const compiler_test_module = b.createModule(.{
        .root_source_file = b.path("src/frontend/compiler/tests.zig"),
        .target = target,
        .optimize = optimize,
    });
    compiler_test_module.addImport("mm0", mm0_lib);

    const compiler_tests = b.addTest(.{
        .root_module = compiler_test_module,
    });
    const run_compiler_tests = b.addRunArtifact(compiler_tests);

    const compiler_bin_test_module = b.createModule(.{
        .root_source_file = b.path("src/bin/compiler/tests.zig"),
        .target = target,
        .optimize = optimize,
    });
    compiler_bin_test_module.addImport("mm0", mm0_lib);
    compiler_bin_test_module.addImport("lsp", lsp_module);

    const compiler_bin_tests = b.addTest(.{
        .root_module = compiler_bin_test_module,
    });
    const run_compiler_bin_tests = b.addRunArtifact(compiler_bin_tests);

    const integration_test_module = b.createModule(.{
        .root_source_file = b.path("tests/integration_examples.zig"),
        .target = target,
        .optimize = optimize,
    });
    integration_test_module.addImport("mm0", mm0_lib);

    const integration_tests = b.addTest(.{
        .root_module = integration_test_module,
    });
    const run_integration_tests = b.addRunArtifact(integration_tests);

    const unit_step = b.step("test-unit", "Run unit tests");
    unit_step.dependOn(&run_trusted_tests.step);
    unit_step.dependOn(&run_root_tests.step);
    unit_step.dependOn(&run_frontend_tests.step);
    unit_step.dependOn(&run_compiler_tests.step);
    unit_step.dependOn(&run_compiler_bin_tests.step);

    const integration_step = b.step(
        "test-integration",
        "Run integration tests against mm0 examples",
    );
    integration_step.dependOn(&run_integration_tests.step);

    const test_step = b.step("test", "Run all tests");
    test_step.dependOn(&run_trusted_tests.step);
    test_step.dependOn(&run_root_tests.step);
    test_step.dependOn(&run_frontend_tests.step);
    test_step.dependOn(&run_compiler_tests.step);
    test_step.dependOn(&run_compiler_bin_tests.step);
    test_step.dependOn(&run_integration_tests.step);
}
