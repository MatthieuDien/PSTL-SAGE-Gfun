#!/bin/bash

SAGE_ROOT="/Vrac/sage-5.7"
SAGE_BIN="$SAGE_ROOT/sage"

if [[ `$SAGE_BIN -branch` != "test" ]]; then
	echo "Changing the sage's current branch to test"
	$SAGE_BIN -b test
fi

if [[ $? -ne 0 ]]; then
	echo -e "\nThe test branch doesn't exist"
	echo "We create it"
	$SAGE_BIN -b main
	$SAGE_BIN -clone test
	$SAGE_BIN -b test
fi


echo -e "\nCopying the files\n"
cp -v multivariate_series.py all.py $SAGE_ROOT/devel/sage-test/sage/combinat/species/

echo -e "\nCompiling the branch\n"
$SAGE_BIN -b test

echo -e "\nDone\n"
