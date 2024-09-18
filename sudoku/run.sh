#!/usr/bin/env bash

TIMEOUT=$1
CMD="timeout $TIMEOUT ./dpll --sudoku"
FILE="sudoku/sudoku.csv"
FROM=$2
TOTAL=$3

pass=0
timeout=0
fail=0

echo ""
echo "------------------------"
echo "  Sudoku Solver         "
echo "------------------------"

for i in $(seq 1 $TOTAL); do
    line=$((i+FROM));
    content=$(sed -n "$line p" $FILE);
    $CMD $content;
    ret=$?;
    if [ $ret -eq 124 ];
    then
	timeout=$((timeout+1));
	echo "$line: \033[0;33mTIMEOUT\033[0m";
    elif [ $ret -ne 0 ];
    then
	 fail=$((fail+1));
	 echo "$line: \033[0;36mFAIL\033[0m";
    else
	pass=$((pass+1));
	echo "$line: \033[0;32mSUCCESS\033[0m"
    fi;
done

echo "------------------------"
echo "\033[0;32mPass   : $pass / $TOTAL\033[0m"
echo "\033[0;33mTimeout: $timeout / $TOTAL\033[0m"
echo "\033[0;36mFail   : $fail / $TOTAL\033[0m"
exit 0
