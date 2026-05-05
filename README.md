# Lean 4 Formalisations for Prime-Power-Free Fibonacci Sequences

This repository contains Lean 4 formalisations of Prime-Power-Free Fibonacci Sequences related to the works of **Nicol** and **Vsemirnov**.

## Prerequisites

* **Lean 4**: Installed via `elan`.
* **VS Code**: With the official **Lean 4 extension**.
* **Mathlib4**: This project relies on the Lean mathematical library.

## How to Run and Build

1. **Download Mathlib Dependencies**: Run `lake exe cache get` in your terminal to fetch pre-compiled binaries.
2. **Build the Project**: Run `lake build` to compile all files and verify the proofs via command line.
3. **Interactive Mode (Recommended)**: Open the project root folder in **VS Code** and open any `.lean` file (e.g., `Nicol/ModularCertificate.lean`).

## Directory Structure

* **Nicol/**: Proofs (Basic, Covering, ModularCertificate).
* **Vsemirnov/**: Proofs (Basic, Covering, ModularCertificate).
* **Nicol.lean & Vsemirnov.lean**: Main files used to import the respective libraries.
* **lakefile.toml**: Package configuration and dependencies.

## Author
- **Simone Cammarasana**
