# Lean 4 Formalizations for Fibonacci Number Theory

This repository contains Lean 4 proofs and formalizations of number theory results concerning Fibonacci numbers, specifically focusing on the works of **Nicol** and **Vsemirnov**.

## Project Overview

The project is organized into two main components:
- **Nicol's Work**: Formalization of covering systems and modular certificates related to Fibonacci sequences.
- **Vsemirnov's Work**: Proofs regarding specific properties and identities within Fibonacci number theory.

## Prerequisites

To interact with these proofs, you need:
* **Lean 4**: Installed via `elan`.
* **VS Code**: With the official **Lean 4 extension**.
* **Mathlib4**: This project relies on the Lean mathematical library.

## How to Run and Build

Once the project is on your machine, follow these steps to initialize and run the environment:

1. **Download Mathlib Dependencies**: Run `lake exe cache get` in your terminal to fetch pre-compiled binaries and avoid long compilation times.
2. **Build the Project**: Run `lake build` to compile all files and verify the proofs via command line.
3. **Interactive Mode (Recommended)**: Open the project root folder in **VS Code** and open any `.lean` file (e.g., `Nicol/ModularCertificate.lean`). The **Lean Infoview** will open on the right (or press `Ctrl+Shift+Enter`), allowing you to move your cursor through the tactics to see the live goal state.

## Directory Structure

* **Nicol/**: Detailed proofs (Basic, Covering, ModularCertificate).
* **Vsemirnov/**: Vsemirnov-specific formalizations.
* **Nicol.lean** & **Vsemirnov.lean**: Library entry points.
* **lakefile.toml**: Package configuration and dependencies.

## Author
- **Simone**
