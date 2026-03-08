const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const mm0_lib = b.createModule(.{
        .root_source_file = b.path("src/lib.zig"),
        .target = target,
        .optimize = optimize,
    });

    const verifier_module = b.createModule(.{
        .root_source_file = b.path("src/main.zig"),
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
        .root_source_file = b.path("src/compiler_main.zig"),
        .target = target,
        .optimize = optimize,
    });
    compiler_module.addImport("mm0", mm0_lib);

    const compiler_exe = b.addExecutable(.{
        .name = "mm0-zigc",
        .root_module = compiler_module,
    });
    b.installArtifact(compiler_exe);

    const run_step = b.step("run", "Run the mm0-zig verifier");
    const run_cmd = b.addRunArtifact(verifier_exe);
    run_step.dependOn(&run_cmd.step);
    run_cmd.step.dependOn(b.getInstallStep());

    const run_compiler_step = b.step(
        "run-compiler",
        "Run the mm0-zig compiler skeleton",
    );
    const run_compiler_cmd = b.addRunArtifact(compiler_exe);
    run_compiler_step.dependOn(&run_compiler_cmd.step);
    run_compiler_cmd.step.dependOn(b.getInstallStep());

    if (b.args) |args| {
        run_cmd.addArgs(args);
        run_compiler_cmd.addArgs(args);
    }

    const unit_test_module = b.createModule(.{
        .root_source_file = b.path("tests/unit_tests.zig"),
        .target = target,
        .optimize = optimize,
    });
    unit_test_module.addImport("mm0", mm0_lib);

    const unit_tests = b.addTest(.{
        .root_module = unit_test_module,
    });
    const run_unit_tests = b.addRunArtifact(unit_tests);

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
    unit_step.dependOn(&run_unit_tests.step);

    const integration_step = b.step(
        "test-integration",
        "Run integration tests against mm0 examples",
    );
    integration_step.dependOn(&run_integration_tests.step);

    const test_step = b.step("test", "Run all tests");
    test_step.dependOn(&run_unit_tests.step);
    test_step.dependOn(&run_integration_tests.step);
}
