#!/bin/bash

# Any error in this file should immediately stop the build.
set -e

# Some dependencies take quite a while to compile, and Travis fails because of this.
# These lines solve this issue by regularly printing on the terminal.
( sleep 60;
	KEEPTRAVISALIVE=1
	while true; do
		sleep 60;
		let "KEEPTRAVISALIVE+=1";
		echo "Compilation takes a while (currently $KEEPTRAVISALIVE minutes): keeping Travis alive.";
	done ) &

# Travis has some limits in the time a build can run.
# The issue is that our dependencies take quite a long time to compile… and Travis reaches the time limit because these dependencies are using all the available time.
# However, if the dependencies are already compiled and cached, Travis provides plenty of time to compile the project.
# This piece of code branches over the environment variable $TRAVISONLYBUILDDEPS between the normal build and only the build of the dependencies.

if [ -z ${TRAVISONLYBUILDDEPS+x} ]; then
	echo '+esy';
	esy
	echo '+esy test';
	esy test
	echo '+esy doc';
	esy doc
else
	case $TRAVISONLYBUILDDEPS in
		all|"")
			echo 'Variable $TRAVISONLYBUILDDEPS is set: only building dependencies.';
			esy build-dependencies --all
			;;
		*)
			echo "Variable \$TRAVISONLYBUILDDEPS is set to '$TRAVISONLYBUILDDEPS': only building this dependency.";
			esy build-dependencies --package=$TRAVISONLYBUILDDEPS
			;;
	esac
fi

