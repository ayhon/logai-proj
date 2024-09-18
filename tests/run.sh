#!/bin/bash

pass=0
wrong=0
timeout=0
fail=0


OKFILES=$(find ./tests/OK -name "*.cnf")
KOFILES=$(find ./tests/KO -name "*.cnf")
echo "find ./tests/KO -path '$KODIR/*.cnf'"
TOTALOK=$(wc -w <<< "$OKFILES")
TOTALKO=$(wc -w <<< "$KOFILES")
TOTAL=$((TOTALOK+TOTALKO))
TIMEOUT=$1
CMD="timeout $TIMEOUT ./dpll"


echo ""
echo "------------------------"
echo "  Running $TOTALOK satisfiable tests with TIMEOUT=$TIMEOUT"
echo "------------------------"

for i in $OKFILES ; do
    echo -n "$i... " ;
    ret=$($CMD $i);
    if [ $? -eq 124 ];
    then
	timeout=$((timeout+1));
	echo -e "\033[0;33mTIMEOUT\033[0m";
    else
	if echo $ret | grep "true" > /dev/null;
	then
	    pass=$((pass+1));
	    echo -e "\033[0;32mSUCCESS\033[0m"
	elif echo $ret | grep "false" > /dev/null;
	then
	    wrong=$((wrong+1));
	    echo -e "\033[0;31mWRONG\033[0m";
	else
	    fail=$((fail+1));
	    echo -e "\033[0;36mFAIL\033[0m";
	fi;
    fi;
done;

echo ""
echo "------------------------"
echo "  Running $TOTALKO unsatisfiable tests with TIMEOUT=$TIMEOUT"
echo "------------------------"

for i in $KOFILES ; do
    echo -n "$i... " ;
    ret=$($CMD $i);
    if [ $? -eq 124 ];
    then
	timeout=$((timeout+1));
	echo -e "\033[0;33mTIMEOUT\033[0m";
    else
	if echo $ret | grep "true" > /dev/null;
	then
	    wrong=$((wrong+1));
	    echo -e "\033[0;31mWRONG\033[0m";
	elif echo $ret | grep "false" > /dev/null;
	then
	    pass=$((pass+1));
	    echo -e "\033[0;32mSUCCESS\033[0m"
	else
	    fail=$((fail+1));
	    echo -e "\033[0;36mFAIL\033[0m";
	fi;
    fi;
done;

echo "------------------------"
echo -e "\033[0;31mWrong  : $wrong / $TOTAL\033[0m"
echo -e "\033[0;32mPass   : $pass / $TOTAL\033[0m"
echo -e "\033[0;33mTimeout: $timeout / $TOTAL\033[0m"
echo -e "\033[0;36mFail   : $fail / $TOTAL\033[0m"
exit 0
