const std = @import("std");

const WebPackageInstall = struct {
    source_dir: []const u8,
    package_name: []const u8,
};

const WEB_PACKAGE_INSTALLS = [_]WebPackageInstall{
    .{ .source_dir = "web/packages/compiler", .package_name = "compiler" },
    .{ .source_dir = "web/packages/verifier", .package_name = "verifier" },
    .{ .source_dir = "web/packages/lsp", .package_name = "lsp" },
};

const WebWasmInstall = struct {
    artifact: *std.Build.Step.Compile,
    package_name: []const u8,
    file_name: []const u8,
};

const WEB_DEMO_FIXTURES = [_][]const u8{
    "hilbert",
    "russell",
    "tseitin",
    "robinson",
    "aristotle",
    "peirce",
    "gentzen",
    "prawitz",
    "barcan",
    "prior",
    "pnueli",
    "barwise",
    "loeb",
    "church",
    "leibniz",
    "mac_lane",
    "martin_lof",
    "peano",
    "euclid",
    "smullyan",
    "zermelo",
};

fn installWebPackageSet(
    b: *std.Build,
    step: *std.Build.Step,
    install_root: []const u8,
    compiler_wasm: *std.Build.Step.Compile,
    verifier_wasm: *std.Build.Step.Compile,
    lsp_server_wasm: *std.Build.Step.Compile,
) void {
    for (WEB_PACKAGE_INSTALLS) |pkg| {
        const install_pkg = b.addInstallDirectory(.{
            .source_dir = b.path(pkg.source_dir),
            .install_dir = .prefix,
            .install_subdir = b.fmt(
                "{s}/@aufbau/{s}",
                .{ install_root, pkg.package_name },
            ),
        });
        step.dependOn(&install_pkg.step);
    }

    const wasm_installs = [_]WebWasmInstall{
        .{
            .artifact = compiler_wasm,
            .package_name = "compiler",
            .file_name = "compiler.wasm",
        },
        .{
            .artifact = verifier_wasm,
            .package_name = "verifier",
            .file_name = "verifier.wasm",
        },
        .{
            .artifact = lsp_server_wasm,
            .package_name = "lsp",
            .file_name = "lsp.wasm",
        },
    };

    for (wasm_installs) |wasm| {
        const install_wasm = b.addInstallArtifact(wasm.artifact, .{
            .dest_dir = .{ .override = .prefix },
            .dest_sub_path = b.fmt(
                "{s}/@aufbau/{s}/{s}",
                .{ install_root, wasm.package_name, wasm.file_name },
            ),
        });
        step.dependOn(&install_wasm.step);
    }
}

fn installWebDemoFixtures(b: *std.Build, step: *std.Build.Step) void {
    const install_web_assets = b.addInstallDirectory(.{
        .source_dir = b.path("web"),
        .install_dir = .prefix,
        .install_subdir = "web-demo",
    });
    step.dependOn(&install_web_assets.step);

    const install_web_fonts = b.addInstallDirectory(.{
        .source_dir = b.path("web/fonts"),
        .install_dir = .prefix,
        .install_subdir = "web-demo/fonts",
    });
    step.dependOn(&install_web_fonts.step);

    for (WEB_DEMO_FIXTURES) |fixture| {
        const install_mm0 = b.addInstallFile(
            b.path(b.fmt("tests/proof_cases/{s}.mm0", .{fixture})),
            b.fmt("web-demo/fixtures/{s}.mm0", .{fixture}),
        );
        step.dependOn(&install_mm0.step);

        const install_proof = b.addInstallFile(
            b.path(b.fmt("tests/proof_cases/{s}.auf", .{fixture})),
            b.fmt("web-demo/fixtures/{s}.auf", .{fixture}),
        );
        step.dependOn(&install_proof.step);
    }
}

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});
    const lsp_dep = b.dependency("lsp_kit", .{});
    const lsp_module = lsp_dep.module("lsp");
    const lsp_types_module = lsp_dep.module("lsp-types");

    const mm0_lib = b.createModule(.{
        .root_source_file = b.path("src/lib.zig"),
        .target = target,
        .optimize = optimize,
    });

    const lsp_diagnostics_module = b.createModule(.{
        .root_source_file = b.path("src/frontend/lsp/diagnostics.zig"),
        .target = target,
        .optimize = optimize,
    });
    lsp_diagnostics_module.addImport("mm0", mm0_lib);
    lsp_diagnostics_module.addImport("lsp", lsp_module);

    const wasm_target = b.resolveTargetQuery(.{
        .cpu_arch = .wasm32,
        .os_tag = .freestanding,
    });
    const lsp_offsets_wasm_module = b.createModule(.{
        .root_source_file = lsp_dep.path("src/offsets.zig"),
        .target = wasm_target,
        .optimize = optimize,
    });
    lsp_offsets_wasm_module.addImport("types", lsp_types_module);
    const lsp_wasm_module = b.createModule(.{
        .root_source_file = b.path("src/bin/compiler/lsp_wasm_compat.zig"),
        .target = wasm_target,
        .optimize = optimize,
    });
    lsp_wasm_module.addImport("types", lsp_types_module);
    lsp_wasm_module.addImport("offsets", lsp_offsets_wasm_module);
    const mm0_wasm_lib = b.createModule(.{
        .root_source_file = b.path("src/lib.zig"),
        .target = wasm_target,
        .optimize = optimize,
    });

    const lsp_diagnostics_wasm_module = b.createModule(.{
        .root_source_file = b.path("src/frontend/lsp/diagnostics.zig"),
        .target = wasm_target,
        .optimize = optimize,
    });
    lsp_diagnostics_wasm_module.addImport("mm0", mm0_wasm_lib);
    lsp_diagnostics_wasm_module.addImport("lsp", lsp_wasm_module);

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
    compiler_module.addImport("lsp_diagnostics", lsp_diagnostics_module);

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

    const lsp_server_wasm_module = b.createModule(.{
        .root_source_file = b.path("src/bin/compiler/lsp_wasm.zig"),
        .target = wasm_target,
        .optimize = optimize,
    });
    lsp_server_wasm_module.addImport("mm0", mm0_wasm_lib);
    lsp_server_wasm_module.addImport("lsp", lsp_wasm_module);
    lsp_server_wasm_module.addImport(
        "lsp_diagnostics",
        lsp_diagnostics_wasm_module,
    );

    const lsp_server_wasm = b.addExecutable(.{
        .name = "abc-lsp-web",
        .root_module = lsp_server_wasm_module,
    });
    lsp_server_wasm.entry = .disabled;
    lsp_server_wasm.rdynamic = true;
    lsp_server_wasm.export_memory = true;

    const web_demo_step = b.step("web-demo", "Build the browser demo");
    const web_packages_step = b.step(
        "web-packages",
        "Build the redistributable JS/wasm packages",
    );

    installWebPackageSet(
        b,
        web_demo_step,
        "web-demo",
        compiler_wasm,
        verifier_wasm,
        lsp_server_wasm,
    );
    installWebPackageSet(
        b,
        web_packages_step,
        "npm",
        compiler_wasm,
        verifier_wasm,
        lsp_server_wasm,
    );
    installWebDemoFixtures(b, web_demo_step);

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

    const lsp_index_test_module = b.createModule(.{
        .root_source_file = b.path("src/lsp_index_tests.zig"),
        .target = target,
        .optimize = optimize,
    });

    const lsp_index_tests = b.addTest(.{
        .root_module = lsp_index_test_module,
    });
    const run_lsp_index_tests = b.addRunArtifact(lsp_index_tests);

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

    const compiler_search_test_module = b.createModule(.{
        .root_source_file = b.path("src/search_tests.zig"),
        .target = target,
        .optimize = optimize,
    });

    const compiler_search_tests = b.addTest(.{
        .root_module = compiler_search_test_module,
    });
    const run_compiler_search_tests = b.addRunArtifact(
        compiler_search_tests,
    );

    const compiler_bin_test_module = b.createModule(.{
        .root_source_file = b.path("src/bin/compiler/tests.zig"),
        .target = target,
        .optimize = optimize,
    });
    compiler_bin_test_module.addImport("mm0", mm0_lib);
    compiler_bin_test_module.addImport("lsp", lsp_module);
    compiler_bin_test_module.addImport(
        "lsp_diagnostics",
        lsp_diagnostics_module,
    );

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
    unit_step.dependOn(&run_lsp_index_tests.step);
    unit_step.dependOn(&run_compiler_tests.step);
    unit_step.dependOn(&run_compiler_search_tests.step);
    unit_step.dependOn(&run_compiler_bin_tests.step);

    const integration_step = b.step(
        "test-integration",
        "Run integration tests against mm0 examples",
    );
    integration_step.dependOn(&run_integration_tests.step);

    const test_step = b.step("test", "Run all tests");
    test_step.dependOn(unit_step);
    test_step.dependOn(integration_step);
}
