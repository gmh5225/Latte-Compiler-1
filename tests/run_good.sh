#!/bin/bash

../make
clear

for filenameLat in good/*.lat; do
    filenameNoExtension="${filenameLat%%.*}"
    
    echo "Compiling file ${filenameNoExtension}"
    ../latc_llvm $filenameLat > tmp.output

    if [[ $? != 0 ]] 
    then
        echo "Error while compliling ${filenameNoExtension}:"
        cat tmp.output
        exit 1
    fi
       

    echo "Running lli ${filenameNoExtension}"
    lli "${filenameNoExtension}.bc" > tmp.output

    if [[ $? != 0 ]] 
    then
        echo "Error while running lli ${filenameNoExtension}:"
        cat tmp.output
        exit 1
    fi

    echo "Comparing result of ${filenameNoExtension}"
    diff "${filenameNoExtension}.output" tmp.output > diff.output

    if [[ $? != 0 ]] 
    then
        echo "Error while comparing result of ${filenameNoExtension}:"
        cat diff.output
        exit 1
    fi

    echo "\n##################################"
    echo "SUCCESS ${filenameNoExtension}"
    echo "##################################\n"
     fi
done