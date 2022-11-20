#!/bin/bash

make > tmp.output 2>&1

for filename in good/*.lat; do    
    ./latc_llvm $filename &> tmp.txt
    status=$?    

    if [[ $status != 0 ]]
    then
        echo "${filename}  -  ❌" 
        cat tmp.txt
    else
        echo "${filename}  -  ✅" 
    fi
        
    rm tmp.txt
done