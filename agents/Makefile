USER_ANSWERS := questions/user_answers.md
ALL_ISSUES := $(wildcard issues/*.md)
UNREADY_ISSUES := $(wildcard issues/*_unready.md)
READY_ISSUES := $(wildcard issues/*_ready.md)

# Sentinel stamps to track when an agent last processed a specific issue
EXPECTED_GENERATE_STAMPS := $(patsubst issues/%_unready.md,issues/.%_generate.stamp,$(UNREADY_ISSUES))
EXPECTED_PLAN_STAMPS := $(patsubst issues/%_ready.md,plans/.%_plan.stamp,$(READY_ISSUES))

.PHONY: all setup triage generate plan

# A single pass evaluates the current files and triggers what's out of date
all: triage generate plan

setup:
	mkdir -p issues questions plans
	touch $(USER_ANSWERS)

# 1. Triager reacts to ANY modified issue files or updated user answers
triage: .triage.sentinel

.triage.sentinel: $(ALL_ISSUES) $(USER_ANSWERS)
	@if ls issues/*.md 1> /dev/null 2>&1; then \
		echo "--- Triaging Issues ---"; \
		aider --message-file issue_triager.txt issues/*.md questions/*.md; \
	fi
	@touch .triage.sentinel

# 2. Generator reacts to modified unready issues
generate: triage $(EXPECTED_GENERATE_STAMPS)

issues/.%_generate.stamp: issues/%_unready.md $(USER_ANSWERS)
	@echo "--- Generating ready issue for $< ---"
	aider --message-file issue_generator.txt $< questions/*.md
	@touch $@

# 3. Planner reacts to modified ready issues
plan: generate $(EXPECTED_PLAN_STAMPS)

plans/.%_plan.stamp: issues/%_ready.md $(USER_ANSWERS)
	@echo "--- Planning modifications for $< ---"
	aider --message-file modification_planner.txt $< questions/*.md plans/
	@touch $@
