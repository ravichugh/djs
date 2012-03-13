#!/bin/bash

echo -e "\e[1;31m"
echo -e "***************************************************************"
echo -e "NEGATIVE TESTS"
echo -e "\e[0m"

for FN in `ls $DJS_DIR/tests/imperative/*/xx*.dref.ml`
do
  echo -n "$FN  "
  ./system-d $FN | tail -1
done

echo -e "\e[1;32m"
echo -e "***************************************************************"
echo -e "POSITIVE TESTS"
echo -e "\e[0m"

for FN in `ls $DJS_DIR/tests/imperative/*/[^_x][^_x]*.dref.ml`
do
  echo -n "$FN  "
  ./system-d $FN | tail -1
done

