cat *.gcc.kvx.s|cut -f2|cut -d' ' -f1|sort -u|grep -v ':'|grep -v -F '.' > gcc_vocabulary.txt
cat *.ccomp.kvx.s|cut -f2|cut -d' ' -f1|sort -u|grep -v ':'|grep -v -F '.' > ccomp_vocabulary.txt
