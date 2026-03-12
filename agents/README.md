# Agentic Workflow

This directory contains a multi-agent workflow powered by `aider` for managing large code modifications. 

## Setup

Initialize the required directories and state files:
```bash
cd agents
mkdir -p issues plans
touch questions.md triage.md
```

## Bootstrapping

Start the workflow by creating your first general issue in the `issues/` directory:
```bash
echo "We need to refactor the database layer to use async I/O. Please figure out what needs to change." > agents/issues/db_refactor.md
```

## Running the Workflow

Because the `Makefile` relies on file dependencies, you trigger the pipeline by asking `make` to build the target plan file. This will automatically invoke the Triager, then the Generator, and finally the Planner:
```bash
cd agents
make plans/db_refactor.md
```
Or, you can just run the triager to process the raw issues:
```bash
make triage.md
```

## Agent Roles
- **Issue Triager**: Prioritizes, deduplicates, and splits issues. Marks actionable issues by renaming them to end with `_unready.md`. Keeps track of its internal state in `triage.md`.
- **Issue Generator**: Expands `_unready.md` issues with requirements and acceptance criteria, and generates a new, fully fleshed out `_ready.md` file.
- **Modification Planner**: Takes `_ready.md` issues and writes a detailed step-by-step coding plan into a corresponding file in the `agents/plans/` directory.

## User Interaction
If agents get stuck, need clarification, or want to raise questions, they will write them in `agents/questions.md`.
You should periodically respond to them by editing `agents/questions.md`. The agents are instructed to check this file for your feedback during their next run.
