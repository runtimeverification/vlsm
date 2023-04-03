for file in `find theories/VLSM/Core/ELMO/ -maxdepth 1 -name '*.v'`; do
   fline=`cat $file | head -n1`
   if [[ $fline == 'Set Default Proof Using "Type".' ]]; then
      echo $file
      echo "already parsed"
   else
      echo $file
      echo -e "Set Default Proof Using \"Type\".\n$(cat $file)" > $file
      OUTPUT=`make "${file}o" 2>&1 1>/dev/null`
      while [[ `echo $OUTPUT | wc -w` > 0 ]]; do
         echo "try again"
         ADD="Proof using "`echo -e $OUTPUT | grep -o -E "but not declared: [, _[:alnum:]]*\." | sed 's/but not declared: //'`
         LINE=`echo $OUTPUT | grep "line.*characters.*" | cut -d' ' -f4 | cut -d',' -f1`
         PLINE=`cat $file | head -n $LINE | grep -n "Proof\." | tail -n -1 | cut -d':' -f1`
         echo $PLINE
         cat $file | head -n $PLINE | tail -n -1
         sed -i "${PLINE}s/Proof\./${ADD}/" $file
         cat $file | head -n $PLINE | tail -n -1
         OUTPUT=`make "${file}o" 2>&1 1>/dev/null`
      done
   fi
done

