.PHONY: all triage.md generate_issues generate_plans

UNREADY_ISSUES = $(wildcard issues/*_unready.md)
READY_ISSUES   = $(wildcard issues/*_ready.md)

# Define the repository files to be provided as read-only context
AIDER ?= aider --yes --read ../array.pl --read ../runtime_prolog.pl --read ../view.pl --no-auto-lint --no-gitignore --model gemini --no-auto-commits

all: triage.md
	@$(MAKE) generate_issues
	@$(MAKE) generate_plans

generate_issues: $(UNREADY_ISSUES:_unready.md=_ready.md)

generate_plans: $(READY_ISSUES:issues/%_ready.md=plans/%.md)

# triage always run, uses triage.md as its state generate unready issues
triage.md: questions.md
	@echo "--- Triaging Issues ---"
	$(AIDER) --message-file issue_triager.txt triage.md issues/*.md questions.md

# each issue generating depends on triaging
issues/%_ready.md: issues/%_unready.md questions.md triage.md
	@echo "--- Generating ready issue for $< ---"
	$(AIDER) --message-file issue_generator.txt $@ $< questions.md

# plan generation depends on ready issue
plans/%.md: issues/%_ready.md questions.md
	@echo "--- Planning modifications for $< ---"
	$(AIDER) --message-file modification_planner.txt $@ $< questions.md
	@touch $@
