# Agentic Workflow

This directory contains a multi-agent workflow powered by `aider` for managing large code modifications. 

## Setup

Initialize the required directories and state files:
```bash
cd agents
make setup
```

## Bootstrapping

Start the workflow by creating your first general issue in the `issues/` directory:
```bash
echo "We need to refactor the database layer to use async I/O. Please figure out what needs to change." > agents/issues/db_refactor.md
```

## Running the Workflow

Run the automated loop (by default, it loops 3 times to allow agents to pass tasks down the pipeline):
```bash
cd agents
make loop
```

## Agent Roles
- **Issue Triager**: Prioritizes, deduplicates, and splits issues. Marks actionable issues as `_unready.md`.
- **Issue Generator**: Expands `_unready.md` issues with requirements and acceptance criteria. Marks them as `_ready.md`.
- **Modification Planner**: Takes `_ready.md` issues and writes a detailed step-by-step coding plan in `agents/plans/`. Marks the issue as `_planned.md`.

## User Interaction
If agents get stuck or need clarification, they will write markdown files in the `agents/questions/` directory.
You should periodically respond to them by editing `agents/questions/user_answers.md`. The agents are instructed to check this file for your feedback during their next run.
