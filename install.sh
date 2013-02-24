#!/bin/bash

if [[ $EUID -ne 0 ]]; then
   echo "You must be root to do this." 1>&2
   exit 100
fi

echo "Changing the sage's current branch to test"
sage -b test

if [[ $? -ne 0 ]]; then
	echo -e "\nThe test branch doesn't exist"
	echo "We create it"
	sage -b main
	sage -clone test
	sage -b test
fi

SAGE_ROOT = `sage -root`

echo -e "\nCopying the files\n"
cp -v multivariate_series.py all.py $SAGE_ROOT/devel/sage-test/sage/combinat/species/

echo -e "\nCompiling the branch\n"
sage -b test

echo -e "\nDone\n"
