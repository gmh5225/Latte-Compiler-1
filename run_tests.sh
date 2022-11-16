#!/bin/bash

make > tmp.output 2>&1

if [[ $? != 0 ]] 
then
        printf  "###### Error while make ❌:\n\n"
        cat tmp.output
        exit 1
fi
# printf  "###### Run make ✅\n\n"

for filenameLat in tests/mine/*.lat; do
    filenameNoExtension="${filenameLat%%.*}"
    
    ./latc_llvm $filenameLat > tmp.output

    if [[ $? != 0 ]] 
    then
        echo "###### Error while compliling ${filenameNoExtension}❌:\n\n"
        cat tmp.output
        exit 1
    fi
    # printf "###### Compiling file ${filenameNoExtension} ✅\n"

    lli "${filenameNoExtension}.bc" > tmp.output

    if [[ $? != 0 ]] 
    then
        printf "Error while running lli ${filenameNoExtension}❌:\n\n"
        cat tmp.output
        exit 1
    fi

    # printf "###### Running lli ${filenameNoExtension} ✅\n"



    diff "${filenameNoExtension}.output" tmp.output > diff.output 2>&1

    if [[ $? != 0 ]] 
    then
        printf "###### Error while comparing result of ${filenameNoExtension}❌:\n\n"
        cat diff.output
        exit 1
    fi
    line=$(head -n 1 ${filenameNoExtension}.lat)

    # printf "###### Comparing result of ${filenameNoExtension} ✅\n"
    printf "${line} ✅\n"

    
done