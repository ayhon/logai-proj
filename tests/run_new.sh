#!/usr/bin/env bash

CALL_PATH="$(dirname "$0")"

RESULT_PASS=0
RESULT_WRONG=0
RESULT_TIMEOUT=0
RESULT_FAIL=0
TOTAL=0

TIMEOUT=${1:-30}
CMD="timeout ${TIMEOUT} ./dpll --proof"
CMD_PROOF="picosat"


function displayWrong()   { tput setaf 1; echo "WRONG";   RESULT_WRONG=$(( RESULT_WRONG + 1 ));    tput setaf 7; }
function displaySuccess() { tput setaf 2; echo "SUCCESS"; RESULT_PASS=$(( RESULT_PASS + 1 ));      tput setaf 7; }
function displayTimeout() { tput setaf 3; echo "TIMEOUT"; RESULT_TIMEOUT=$(( RESULT_TIMEOUT + 1)); tput setaf 7; }
function displayFail()    { tput setaf 4; echo "FAIL";    RESULT_FAIL=$(( RESULT_FAIL + 1 ));      tput setaf 7; }

# void launchSatisfiableTest(String filePath)
function launchSatisfiableTest()
{
    local FILEPATH="$1"

    echo -n "${FILEPATH}... "

    RESULT=$(${CMD} "${FILEPATH}")

    if [[ $? -eq 124 ]]; then
        displayTimeout
    else
        if [[ ${RESULT} = true* ]]; then
            local PROOF=$(echo " ${RESULT:6}" | tr '\n' ' ' | sed 's/ / -a /g')
            local CHECK=$(${CMD_PROOF} "${FILEPATH}" ${PROOF:1:-4})

            if [[ ${CHECK:2} = SATISFIABLE* ]]; then
                displaySuccess
            else
                displayWrong
            fi

        elif [[ ${RESULT} = false ]]; then
            displayWrong
        else
            displayFail
        fi
    fi
}

# void launchUnsatisfiableTest(String filePath)
function launchUnsatisfiableTest()
{
    local FILEPATH="$1"

    echo -n "${FILEPATH}... "

    RESULT=$(${CMD} "${FILEPATH}")

    if [[ $? -eq 124 ]]; then
        displayTimeout
    else
        if [[ ${RESULT} = true* ]]; then
            displayWrong
        elif [[ ${RESULT} = false ]]; then
            displaySuccess
        else
            displayFail
        fi
    fi
}


echo ""
echo "------------------------"
echo "  Running satisfiable tests with TIMEOUT=$TIMEOUT"
echo "------------------------"

while IFS= read -r -d '' FILE; do

    launchSatisfiableTest "${FILE}"

    TOTAL=$(( TOTAL + 1 ))

done < <(find "${CALL_PATH}/OK" -name "*.cnf" -print0)


echo ""
echo "------------------------"
echo "  Running unsatisfiable tests with TIMEOUT=$TIMEOUT"
echo "------------------------"

while IFS= read -r -d '' FILE; do

    launchUnsatisfiableTest "${FILE}"

    TOTAL=$(( TOTAL + 1 ))

done < <(find "${CALL_PATH}/KO" -name "*.cnf" -print0)


tput setaf 1; echo "Wrong  : ${RESULT_WRONG} / ${TOTAL}"; tput setaf 7
tput setaf 2; echo "Pass   : ${RESULT_PASS} / ${TOTAL}"; tput setaf 7
tput setaf 3; echo "Timeout: ${RESULT_TIMEOUT} / ${TOTAL}"; tput setaf 7
tput setaf 4; echo "Fail   : ${RESULT_FAIL} / ${TOTAL}"; tput setaf 7
