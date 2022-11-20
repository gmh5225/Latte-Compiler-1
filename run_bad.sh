#!/bin/bash

make > tmp.output 2>&1

for filename in bad/*.lat; do    
    ./latc_llvm $filename > tmp.txt 2>&1
    status=$?    

    if [[ $status = 0 ]]
    then
        echo "${filename}  -  ❌" 
        cat tmp.txt
    else
        echo "${filename}  -  ✅" 
    fi
        
    rm tmp.txt
done