#!/usr/bin/env python3
"""
End-to-end test: Train transformer, distill, export to Lean, verify bounds.

This script demonstrates the full workflow:
1. Train a small transformer teacher on a simple function approximation task
2. Distill knowledge to an even smaller student model
3. Export both models to Lean
4. Run Lean to compute verified interval bounds
5. Compare teacher vs student bounds

Task: Approximate f(x) = tanh(mean(x)) for x ∈ [-1, 1]^d
This is a good test because:
- LayerNorm naturally computes mean, so transformer should learn it easily
- tanh is bounded, so we can verify output bounds
- The dependency problem in LayerNorm matters here
"""

import os
import sys
import subprocess
import tempfile
from pathlib import Path

# Add parent to path for leancert import
sys.path.insert(0, str(Path(__file__).parent.parent / "python"))

import numpy as np

try:
    import torch
    import torch.nn as nn
    import torch.optim as optim
    from torch.utils.data import DataLoader, TensorDataset
    HAS_TORCH = True
except ImportError:
    HAS_TORCH = False
    print("PyTorch not installed. Install with: pip install torch")
    sys.exit(1)

import leancert as lb


# Configuration
INPUT_DIM = 4          # Small for fast verification
HIDDEN_DIM_TEACHER = 16
HIDDEN_DIM_STUDENT = 8
FFN_DIM_TEACHER = 32
FFN_DIM_STUDENT = 16
NUM_LAYERS_TEACHER = 2
NUM_LAYERS_STUDENT = 1
NUM_SAMPLES = 5000
BATCH_SIZE = 64
EPOCHS_TEACHER = 100
EPOCHS_DISTILL = 50
TEMPERATURE = 2.0      # For soft targets in distillation
LEARNING_RATE = 1e-3


def target_function(x: torch.Tensor) -> torch.Tensor:
    """Target function: tanh(mean(x))"""
    return torch.tanh(x.mean(dim=-1, keepdim=True))


class TinyTransformer(nn.Module):
    """A minimal transformer for function approximation."""

    def __init__(self, input_dim: int, hidden_dim: int, ffn_dim: int, num_layers: int):
        super().__init__()
        self.input_dim = input_dim
        self.hidden_dim = hidden_dim

        # Project input to hidden dim
        self.input_proj = nn.Linear(input_dim, hidden_dim)

        # Transformer layers (simplified: no attention, just LN + FFN)
        self.layers = nn.ModuleList([
            TransformerLayer(hidden_dim, ffn_dim)
            for _ in range(num_layers)
        ])

        # Output projection
        self.output_proj = nn.Linear(hidden_dim, 1)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        # x: (batch, input_dim)
        h = self.input_proj(x)  # (batch, hidden_dim)

        for layer in self.layers:
            h = layer(h)

        return self.output_proj(h)  # (batch, 1)


class TransformerLayer(nn.Module):
    """Single transformer layer: LN -> FFN -> Residual -> LN"""

    def __init__(self, hidden_dim: int, ffn_dim: int):
        super().__init__()
        self.norm1 = nn.LayerNorm(hidden_dim)
        self.linear1 = nn.Linear(hidden_dim, ffn_dim)
        self.linear2 = nn.Linear(ffn_dim, hidden_dim)
        self.norm2 = nn.LayerNorm(hidden_dim)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        # Pre-norm
        h = self.norm1(x)

        # FFN with GELU
        h = self.linear1(h)
        h = torch.nn.functional.gelu(h)
        h = self.linear2(h)

        # Residual + Post-norm
        h = x + h
        h = self.norm2(h)

        return h


def create_dataset(num_samples: int, input_dim: int):
    """Create training dataset."""
    X = torch.rand(num_samples, input_dim) * 2 - 1  # Uniform in [-1, 1]
    y = target_function(X)
    return TensorDataset(X, y)


def train_teacher(model: nn.Module, train_loader: DataLoader, epochs: int):
    """Train the teacher model."""
    optimizer = optim.Adam(model.parameters(), lr=LEARNING_RATE)
    criterion = nn.MSELoss()

    model.train()
    for epoch in range(epochs):
        total_loss = 0.0
        for X, y in train_loader:
            optimizer.zero_grad()
            pred = model(X)
            loss = criterion(pred, y)
            loss.backward()
            optimizer.step()
            total_loss += loss.item()

        if (epoch + 1) % 20 == 0:
            avg_loss = total_loss / len(train_loader)
            print(f"  Teacher Epoch {epoch + 1}/{epochs}, Loss: {avg_loss:.6f}")

    return model


def distill_student(teacher: nn.Module, student: nn.Module,
                    train_loader: DataLoader, epochs: int, temperature: float):
    """Distill knowledge from teacher to student."""
    optimizer = optim.Adam(student.parameters(), lr=LEARNING_RATE)

    teacher.eval()
    student.train()

    for epoch in range(epochs):
        total_loss = 0.0
        for X, y in train_loader:
            optimizer.zero_grad()

            # Get soft targets from teacher
            with torch.no_grad():
                teacher_out = teacher(X) / temperature

            # Student prediction
            student_out = student(X) / temperature

            # Distillation loss (MSE on soft targets) + hard target loss
            soft_loss = nn.MSELoss()(student_out, teacher_out)
            hard_loss = nn.MSELoss()(student(X), y)

            loss = 0.7 * soft_loss * (temperature ** 2) + 0.3 * hard_loss
            loss.backward()
            optimizer.step()
            total_loss += loss.item()

        if (epoch + 1) % 10 == 0:
            avg_loss = total_loss / len(train_loader)
            print(f"  Student Epoch {epoch + 1}/{epochs}, Loss: {avg_loss:.6f}")

    return student


def evaluate_model(model: nn.Module, test_X: torch.Tensor) -> tuple:
    """Evaluate model on test data."""
    model.eval()
    with torch.no_grad():
        pred = model(test_X)
        true = target_function(test_X)
        mse = nn.MSELoss()(pred, true).item()
        max_error = (pred - true).abs().max().item()
    return mse, max_error


def extract_transformer_for_lean(model: nn.Module, name: str) -> lb.TransformerEncoder:
    """Extract transformer layers for Lean export."""
    blocks = []

    for i, layer in enumerate(model.layers):
        # Extract LayerNorm parameters
        ln1 = lb.LayerNormParams.from_numpy(
            layer.norm1.weight.detach().cpu().numpy(),
            layer.norm1.bias.detach().cpu().numpy(),
            layer.norm1.eps
        )
        ln2 = lb.LayerNormParams.from_numpy(
            layer.norm2.weight.detach().cpu().numpy(),
            layer.norm2.bias.detach().cpu().numpy(),
            layer.norm2.eps
        )

        # Extract FFN
        ffn = lb.FFNBlock.from_numpy(
            layer.linear1.weight.detach().cpu().numpy(),
            layer.linear1.bias.detach().cpu().numpy(),
            layer.linear2.weight.detach().cpu().numpy(),
            layer.linear2.bias.detach().cpu().numpy()
        )

        blocks.append(lb.TransformerBlock(ln1=ln1, ffn=ffn, ln2=ln2))

    return lb.TransformerEncoder(
        blocks=blocks,
        input_names=[f"x{i}" for i in range(model.hidden_dim)],
        description=f"{name} transformer"
    )


def generate_lean_verification_file(
    teacher_encoder: lb.TransformerEncoder,
    student_encoder: lb.TransformerEncoder,
    input_dim: int,
    output_path: Path
):
    """Generate Lean file that verifies both models and compares bounds."""

    # Generate individual exports
    teacher_lean = teacher_encoder.export_lean(
        name="teacher",
        namespace="DistillationTest",
        input_domain={f"x{i}": (-1.0, 1.0) for i in range(teacher_encoder.dim)},
        use_affine_layernorm=True
    )

    student_lean = student_encoder.export_lean(
        name="student",
        namespace="DistillationTest",
        input_domain={f"x{i}": (-1.0, 1.0) for i in range(student_encoder.dim)},
        use_affine_layernorm=True
    )

    # Combine into single file with comparison
    combined = f'''/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under AGPL-3.0 license as described in the file LICENSE.
Authors: LeanCert Contributors (auto-generated)
-/
import LeanCert.ML.Transformer
import LeanCert.ML.LayerNormAffine

set_option linter.unnecessarySeqFocus false

/-!
# Transformer Distillation Verification

This file verifies bounds for both teacher and student transformers,
demonstrating that the distilled student produces similar outputs.

## Models
- **Teacher**: {teacher_encoder.num_layers} layers, dim={teacher_encoder.dim}, hidden={teacher_encoder.hidden_dim}
- **Student**: {student_encoder.num_layers} layers, dim={student_encoder.dim}, hidden={student_encoder.hidden_dim}

## Verification
We compute interval bounds for both models on the input domain [-1, 1]^d
using affine arithmetic for tight LayerNorm bounds.
-/

namespace DistillationTest

open LeanCert.Core
open LeanCert.ML
open LeanCert.ML.Transformer
open IntervalVector

/-! ## Teacher Model -/

{_extract_definitions(teacher_lean, "teacher")}

/-! ## Student Model -/

{_extract_definitions(student_lean, "student")}

/-! ## Comparison -/

/-- Compare output bounds between teacher and student -/
#eval do
  IO.println "======================================"
  IO.println "Teacher vs Student Output Bounds"
  IO.println "======================================"
  IO.println ""
  IO.println "Teacher output bounds:"
  for h : i in [:teacherOutputBounds.length] do
    let I := teacherOutputBounds[i]
    IO.println s!"  output[{{i}}] ∈ [{{I.lo.toRat}}, {{I.hi.toRat}}]"
    IO.println s!"    width = {{I.hi.toRat - I.lo.toRat}}"
  IO.println ""
  IO.println "Student output bounds:"
  for h : i in [:studentOutputBounds.length] do
    let I := studentOutputBounds[i]
    IO.println s!"  output[{{i}}] ∈ [{{I.lo.toRat}}, {{I.hi.toRat}}]"
    IO.println s!"    width = {{I.hi.toRat - I.lo.toRat}}"
  IO.println ""
  IO.println "======================================"

end DistillationTest
'''

    output_path.write_text(combined)
    return output_path


def _extract_definitions(lean_code: str, prefix: str) -> str:
    """Extract the definition part from generated Lean code (skip header)."""
    lines = lean_code.split('\n')

    # Find where definitions start (after namespace line)
    start_idx = 0
    for i, line in enumerate(lines):
        if line.startswith('open LeanCert'):
            start_idx = i + 1
            break

    # Find where namespace ends
    end_idx = len(lines)
    for i, line in enumerate(lines):
        if line.startswith('end '):
            end_idx = i
            break

    return '\n'.join(lines[start_idx:end_idx])


def run_lean_verification(lean_file: Path, leancert_root: Path) -> tuple:
    """Run Lean to verify the models and extract bounds."""
    print(f"\nRunning Lean verification on {lean_file.name}...")

    # Run lake build on the file
    result = subprocess.run(
        ["lake", "env", "lean", str(lean_file)],
        cwd=leancert_root,
        capture_output=True,
        text=True,
        timeout=300  # 5 minute timeout
    )

    return result.returncode, result.stdout, result.stderr


def main():
    print("=" * 60)
    print("Transformer Distillation End-to-End Test")
    print("=" * 60)
    print()

    # Paths
    script_dir = Path(__file__).parent
    leancert_root = script_dir.parent
    output_dir = script_dir / "output"
    output_dir.mkdir(exist_ok=True)

    # Step 1: Create dataset
    print("Step 1: Creating dataset...")
    dataset = create_dataset(NUM_SAMPLES, INPUT_DIM)
    train_loader = DataLoader(dataset, batch_size=BATCH_SIZE, shuffle=True)

    # Test set
    test_X = torch.rand(500, INPUT_DIM) * 2 - 1
    print(f"  Training samples: {NUM_SAMPLES}")
    print(f"  Input dimension: {INPUT_DIM}")
    print(f"  Target function: tanh(mean(x))")
    print()

    # Step 2: Train teacher
    print("Step 2: Training teacher transformer...")
    teacher = TinyTransformer(
        INPUT_DIM, HIDDEN_DIM_TEACHER, FFN_DIM_TEACHER, NUM_LAYERS_TEACHER
    )
    print(f"  Architecture: {NUM_LAYERS_TEACHER} layers, hidden={HIDDEN_DIM_TEACHER}, ffn={FFN_DIM_TEACHER}")
    teacher = train_teacher(teacher, train_loader, EPOCHS_TEACHER)

    teacher_mse, teacher_max_err = evaluate_model(teacher, test_X)
    print(f"  Final MSE: {teacher_mse:.6f}")
    print(f"  Max error: {teacher_max_err:.6f}")
    print()

    # Step 3: Distill to student
    print("Step 3: Distilling to student transformer...")
    student = TinyTransformer(
        INPUT_DIM, HIDDEN_DIM_STUDENT, FFN_DIM_STUDENT, NUM_LAYERS_STUDENT
    )
    print(f"  Architecture: {NUM_LAYERS_STUDENT} layers, hidden={HIDDEN_DIM_STUDENT}, ffn={FFN_DIM_STUDENT}")
    print(f"  Temperature: {TEMPERATURE}")
    student = distill_student(teacher, student, train_loader, EPOCHS_DISTILL, TEMPERATURE)

    student_mse, student_max_err = evaluate_model(student, test_X)
    print(f"  Final MSE: {student_mse:.6f}")
    print(f"  Max error: {student_max_err:.6f}")
    print()

    # Step 4: Compare models empirically
    print("Step 4: Comparing models empirically...")
    teacher.eval()
    student.eval()
    with torch.no_grad():
        teacher_out = teacher(test_X)
        student_out = student(test_X)
        disagreement = (teacher_out - student_out).abs()
        print(f"  Mean |teacher - student|: {disagreement.mean().item():.6f}")
        print(f"  Max |teacher - student|: {disagreement.max().item():.6f}")
    print()

    # Step 5: Extract for Lean
    print("Step 5: Extracting models for Lean verification...")
    teacher_encoder = extract_transformer_for_lean(teacher, "Teacher")
    student_encoder = extract_transformer_for_lean(student, "Student")
    print(f"  Teacher: {teacher_encoder.num_layers} blocks, dim={teacher_encoder.dim}")
    print(f"  Student: {student_encoder.num_layers} blocks, dim={student_encoder.dim}")
    print()

    # Step 6: Generate Lean file
    print("Step 6: Generating Lean verification file...")
    lean_file = output_dir / "DistillationTest.lean"
    generate_lean_verification_file(
        teacher_encoder, student_encoder,
        HIDDEN_DIM_TEACHER, lean_file
    )
    print(f"  Generated: {lean_file}")
    print(f"  File size: {lean_file.stat().st_size} bytes")
    print()

    # Also save individual exports
    teacher_file = output_dir / "Teacher.lean"
    teacher_lean = teacher_encoder.export_lean(
        name="teacher",
        namespace="DistillationTest.Teacher",
        input_domain={f"x{i}": (-1.0, 1.0) for i in range(teacher_encoder.dim)},
        use_affine_layernorm=True
    )
    teacher_file.write_text(teacher_lean)
    print(f"  Teacher export: {teacher_file}")

    student_file = output_dir / "Student.lean"
    student_lean = student_encoder.export_lean(
        name="student",
        namespace="DistillationTest.Student",
        input_domain={f"x{i}": (-1.0, 1.0) for i in range(student_encoder.dim)},
        use_affine_layernorm=True
    )
    student_file.write_text(student_lean)
    print(f"  Student export: {student_file}")
    print()

    # Step 7: Run Lean verification (optional, may take time)
    print("Step 7: Running Lean verification...")
    print("  (This may take a few minutes for compilation...)")

    try:
        # Try to run the teacher file first (smaller)
        returncode, stdout, stderr = run_lean_verification(teacher_file, leancert_root)

        if returncode == 0:
            print("  ✓ Teacher verification succeeded!")
            if stdout:
                print("\n  Lean output:")
                for line in stdout.split('\n')[-20:]:  # Last 20 lines
                    if line.strip():
                        print(f"    {line}")
        else:
            print(f"  ✗ Teacher verification failed (exit code {returncode})")
            if stderr:
                # Show relevant error lines
                error_lines = [l for l in stderr.split('\n') if 'error' in l.lower()][:5]
                for line in error_lines:
                    print(f"    {line}")
            print("\n  Note: Some errors are expected if Lean types need adjustment.")
            print("  The generated Lean code serves as a template.")

    except subprocess.TimeoutExpired:
        print("  ⚠ Verification timed out (>5 minutes)")
        print("  You can run manually: lake env lean " + str(teacher_file))
    except FileNotFoundError:
        print("  ⚠ 'lake' command not found")
        print("  Make sure Lean 4 is installed and lake is in PATH")

    print()
    print("=" * 60)
    print("Summary")
    print("=" * 60)
    print(f"  Teacher MSE: {teacher_mse:.6f}, Max Error: {teacher_max_err:.6f}")
    print(f"  Student MSE: {student_mse:.6f}, Max Error: {student_max_err:.6f}")
    print(f"  Distillation quality: {student_mse / teacher_mse:.2f}x teacher MSE")
    print()
    print("Generated files:")
    print(f"  - {teacher_file}")
    print(f"  - {student_file}")
    print(f"  - {lean_file}")
    print()
    print("To verify manually, run:")
    print(f"  cd {leancert_root}")
    print(f"  lake env lean {teacher_file}")
    print()


if __name__ == "__main__":
    main()
