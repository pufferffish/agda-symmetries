#!/bin/bash

rm -f Everything.agda

temp=$(mktemp)

echo "{-# OPTIONS --cubical #-}" >> $temp
echo "module Everything where" >> $temp


find . -path ./Experiments -prune -o -name '*.agda' -print0 | while read -d $'\0' file
do
  module=$(echo "$file" | sed -e "s|./||" -e 's|\.agda$||' -e 's|/|.|g')
  echo "open import ${module}" >> $temp
done

mv $temp Everything.agda