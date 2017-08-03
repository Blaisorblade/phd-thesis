#!/bin/sh
#new_snapshot=~/Dropbox/Drafts/thesis-main-$(timestamp)-g$(git describe --always).pdf
new_snapshot=thesis-main-${1/%/-}$(timestamp)-g$(git describe --always).pdf
cp thesis-main.pdf ${new_snapshot}
skim-revert ${new_snapshot}
