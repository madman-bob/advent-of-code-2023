days := $(patsubst Day%,day%,$(wildcard Day*))

.PHONY: $(days)

SESSION_COOKIE ?=

$(days): day%: Day%/input
	idris2 --find-ipkg Day$*/Day$*.idr --exec main

Day%/input:
ifndef SESSION_COOKIE
	@echo "Puzzle inputs differ by user. Set SESSION_COOKIE, or download input $@ manually"
	@exit 1
endif
	@mkdir -p $(@D)
	wget https://adventofcode.com/2023/day/$*/input -O Day$*/input --header "Cookie: session=$(SESSION_COOKIE)"
