.PHONY: triage.md

# triage always run, uses triage.md as its state generate unready issues
triage.md: questions.md
	@echo "--- Triaging Issues ---"
	aider --message-file issue_triager.txt triage.md issues/*.md questions.md

# each issue generating depends on triaging
issues/%_ready.md: issues/%_unready.md questions.md triage.md
	@echo "--- Generating ready issue for $< ---"
	aider --message-file issue_generator.txt $@ $< questions.md

# plan generation depends on ready issue
plans/%.md: issues/%_ready.md questions.md
	@echo "--- Planning modifications for $< ---"
	aider --message-file modification_planner.txt $@ $< questions.md
	@touch $@
