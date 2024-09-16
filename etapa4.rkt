#lang racket
(require "suffix-tree-stream.rkt")
(require "collection.rkt")

(provide (all-defined-out))

;; Vom prelua toate funcțiile din etapele 1-3 (exceptând
;; longest-common-substring, care nu beneficiază de 
;; reprezentarea ca flux întrucât parcurge tot arborele)
;; și le vom adapta la noua reprezentare a unui ST.
;;
;; Pentru că un ST este construit pornind de la o colecție
;; de sufixe și pentru că ne dorim să nu calculăm toate
;; sufixele decât dacă este nevoie, vom modifica toate
;; funcțiile care prelucrau liste de sufixe pentru a
;; prelucra fluxuri de sufixe.
;;
;; Obs: fără această modificare a listelor de sufixe în
;; fluxuri de sufixe, și presupunând că am manipulat
;; arborii de sufixe doar prin interfața definită în
;; fișierul suffix-tree (respectând astfel bariera de 
;; abstractizare), ar trebui să alterăm doar funcția 
;; suffixes->st care este practic un constructor pentru
;; tipul ST.
;; Din cauza transformării listelor de sufixe în fluxuri,
;; avem mult mai multe implementări de modificat.
;; Puteam evita acest lucru? Da, utilizând conceptul de
;; colecție de sufixe de la început (în loc să presupunem
;; că ele vor fi prelucrate ca liste). În loc de cons,
;; car, cdr, map, filter, etc. am fi folosit de fiecare
;; dată collection-cons, collection-first, ... etc. -
;; aceste funcții fiind definite într-o bibliotecă
;; inițială ca fiind echivalentele lor pe liste, și
;; redefinite ulterior în stream-cons, stream-first,
;; ... etc. Operatorii pe colecții de sufixe ar fi 
;; folosit, desigur, doar funcții de tip collection-.
;;
;; Am ales să nu procedăm astfel pentru că ar fi provocat
;; confuzie la momentul respectiv (când chiar operatorii
;; pe liste erau o noutate) și pentru a vă da ocazia să
;; faceți singuri acest "re-design".


; TODO
; Copiați din etapele anterioare implementările funcțiilor
; de mai jos și modificați-le astfel:
; - Toate funcțiile care lucrează cu liste de sufixe vor
;   lucra cu un nou tip de date Collection, ai cărui
;   constructori și operatori vor fi definiți de voi
;   în fișierul collection.rkt.
; - Pentru toate funcțiile, trebuie să vă asigurați că
;   este respectată bariera de abstractizare (atât în 
;   cazul tipului ST cât și în cazul tipului Collection).
; Obs: cu cât mai multe funcții rămân nemodificate, cu atât
; este mai bine (înseamnă că design-ul inițial a fost bun).

(define (longest-common-prefix w1 w2)
  ;; definim o functie auxiliara cu un acumulator pentru prefix
  (define (aux prefix w1 w2)
    (cond
      ;; cazul de baza: daca una dintre liste este vida
      ((or (null? w1) (null? w2))
       ;; daca da, returnam prefixul (acumulat) si listele neschimbate
       ;; cum fiecare caracter comun gasit e lipt in fata prefixului,
       ;; va trebui sa ii dam reverse
       (list (reverse prefix) w1 w2))
      ;; daca nu avem vreo lista vida
      ;; comparam primele caractere
      ((char=? (car w1) (car w2))
       ;; daca sunt egale, trebuie sa construim lista pentru prefix
       (aux (cons (car w1) prefix) (cdr w1) (cdr w2)))
      ;; daca NU au primul caracter comun, returnam prefixul acumulat
      ;; si cele doua liste
      (else
       (list (reverse prefix) w1 w2)
       )
      )
    )
  ;; apelam functia auxiliara cu lista acumulator initiala
  (aux '() w1 w2))


; am schimbat, în numele funcției, cuvântul list în
; cuvântul collection
(define (longest-common-prefix-of-collection words)
  ;; definim o functie auxiliara
  (define (aux words prefix)
    ;; cand colectia de cuvinte devine nula la apel,
    ;; inseamna ca prefixul a fost calculat si il returnam
    ;; am inlocuit null? cu collection-empty?
    (if (collection-empty? words)
        prefix
        ;; calculam cu ajutorul functiei de la TODO 2
        ;; longest-common-prefix dintre primele 2 elemente ale
        ;; listei de cuvinte
        ;; astfel se actualizeaza prefixul la fiecare apel, iar
        ;; lista de cuvinte devine din ce in ce mai scurta,
        ;; eliminandu-se cate un cuvant de la inceput
        (aux (collection-cdr words) (car (longest-common-prefix prefix (collection-car words))))
        )
    )
  (if (collection-empty? words)
      '()
      ;; apelam functia auxiliara,
      ;; pornind cu primul cuvant ca prefix initial
      (aux (collection-cdr words) (collection-car words))))


(define (match-pattern-with-label st pattern)
  ;; branch-ul care incepe cu prima litera din pattern
  (let ((ch-branch (get-ch-branch st (car pattern))))
  (cond
    ;; daca NU exista branch cu litera cautata
    ((not ch-branch)
         (list #f '()))
    (else
     (let* (;; cel mai lung prefix comun dintre pattern si eticheta curenta
            (common-prefix (car (longest-common-prefix pattern (get-branch-label ch-branch))))
            ;; ce ramane din pattern dupa eliminarea celui mai lung prefix
            (new-pattern (cddr (longest-common-prefix (get-branch-label ch-branch) pattern)))
            ;; subarborele corespunzator branch-ului
            (subtree (get-branch-subtree ch-branch)))
       (cond
             ;; daca pattern-ul se gaseste integral in eticheta
             ((equal? common-prefix pattern) #t)
             ;; daca pattern-ul se potriveste cu eticheta dar nu este continut in ea
             ;; adica daca eticheta este un prefix al pattern-ului
             ((equal? common-prefix (get-branch-label ch-branch))
              ;; returnam lista formata din eticheta,
              ;; noul pattern si subarborele branch-ului
              ;; lucru care va ajuta la recursivitatea implementata mai jos
              (list (get-branch-label ch-branch) (car new-pattern) subtree))
       (else
        ;; daca pattern-ul nu s-a potrivit cu eticheta
            (list #f common-prefix))))))))


(define (st-has-pattern? st pattern)
  ;; verificam daca pattern-ul apare in arbore folosind match-pattern-with-label
  (let ((result (match-pattern-with-label st pattern)))
    (cond
      ;; daca rezultatul este #t, atunci pattern-ul se afla sigur in arbore
      ((eq? result #t) #t)
      ;; daca match-pattern-with-label returneaza lista formata din eticheta,
      ;; noul pattern si subarborele branch-ului (verificam asta prin compararea
      ;; primului element din lista cu #f <- NU trebuie sa fie egale),
      ;; atunci facem apelul recursiv pentru subarbore si noul pattern
      ((not (eq? (car result) #f)) (st-has-pattern? (caddr result) (cadr result)))
      ;; altfel, daca ne aflam in al treilea caz, pattern-ul sigur NU se gaseste
      (else #f))))


;; construieste fluxul de sufixe al unui text
(define (get-suffixes text)
  (if (null? text)
      empty-collection
      ;; altfel avem apel recursiv:
      (collection-cons text (get-suffixes (cdr text)))))


(define (get-ch-words words ch)
  ;; filtram cuvintele nevide care au primul caracter ch
  ;; din words
  ;; doar ca de data asta words nu e lista, e collection
  (collection-filter (lambda (word)
                       (and (not (collection-empty? word))
                            (equal? ch (collection-car word))))
                     words))


(define (ast-func suffixes)
  ;; primul caracter
  (define first-ch (car (collection-car suffixes)))
  (if (collection-empty? suffixes) (list '() suffixes)
  ;; returnam lista formata din primul caracter si sufixele
  ;; din care am eliminat first-ch
  ;; folosim map pentru a avea o implementare functionala
  (cons (list first-ch) (collection-map collection-cdr suffixes))))


(define (cst-func suffixes)
  ;; pentru eticheta CST apelam functia longest-common-prefix-of-list
  ;; si vom selecta primul element al listei (prefixul)
  (define label-cst (longest-common-prefix-of-collection suffixes))
  ;; pentru a construi noul sufix, apelam functia longest-common-prefix
  ;; intre eticheta CST si sufixul initial si selectam
  ;; al treilea element
  ;; putem folosi functia map

  ;; definim mai intai o functie care sa fie parametru pentru map
  (define (new-suffix suffix)
    ;; folosim caddr pentru a accesa direct al treilea element
    ;; al listei rezultat
    (if (null?  (longest-common-prefix label-cst suffix)) (list '() suffixes)
    (caddr (longest-common-prefix label-cst suffix)))
    )
  (cons label-cst (collection-map new-suffix suffixes)))


; considerați că și parametrul alphabet este un flux
; (desigur, și suffixes este un flux, fiind o colecție
; de sufixe)
; Funcția pentru calcularea etichetei și noilor sufixe pentru un set de sufixe

(define (suffixes->st labeling-func suffixes alphabet)
  ;; branches contine FLUXUL branchurilor (adica pereche (label, subtree))
  (let* ((branches
           (collection-map (lambda (ch)
                   (let* ((ch-words (get-ch-words suffixes ch))
                          (ch-suffixes (if (collection-empty? ch-words) '() (labeling-func ch-words))))
                     ch-suffixes))
                 alphabet)))
    ;; map care lipeste labelurile pentru fiecare branch din branches (construit mai devreme)
    (collection-map (lambda (branch)
            ;; daca branch-ul curent este null
            (if (null? branch)
                '()
                ;; altfel:
                ;; fiecare branch are un label
                (let ((label (get-branch-label branch))
                      ;; si un subtree
                      (subtree (get-branch-subtree branch)))
                  ;; se construieste perechea (label, subtree)
                  (cons label
                        (if (collection-empty? subtree)
                            empty-collection
                            ;; cu ajutorul apelului recursiv
                            (suffixes->st labeling-func subtree alphabet))))))
                    ;; ii dau in map doar branch-urile nevide
         (collection-filter (lambda (branch) (not (null? branch))) branches))))


; nu uitați să convertiți alfabetul într-un flux
(define text->st
  (lambda (text)
    (lambda (labeling-func)
      ;; adugam dolar la finalul textului
      (define text-dollar (append text (list #\$)))
      ;; obtinem sufixele textului
      (define suffixes (get-suffixes text-dollar))
      ;; obtinem alfabetul sortat asociat textului
      (define alphabet (sort (remove-duplicates text-dollar) char<?))
      ;; convertiam alafabetul intr-un flux
      (define alphabet-stream (list->stream alphabet))
      ;; returnam arborele de sufixe folosind functia de etichetare
      (suffixes->st labeling-func suffixes alphabet-stream))))

(define (list->stream lst)
  (if (null? lst)
      empty-collection
      (collection-cons (car lst) (list->stream (cdr lst)))))


(define (text->ast text)
    ((text->st text) ast-func))


(define (text->cst text)
    ((text->st text) cst-func))


; dacă ați respectat bariera de abstractizare,
; această funcție va rămâne nemodificată.
(define (substring? text pattern)
  (st-has-pattern? (text->ast text) pattern)
  )


; dacă ați respectat bariera de abstractizare,
; această funcție va rămâne nemodificată.
(define (repeated-substring-of-given-length text len)
  ;; arborele de sufixe asociat textului
  (define ST (text->cst text))
  (repeated-substring ST len '())
 )
;; functie care returneaza rezultatul cautat
(define (repeated-substring ST len acc)
  ;; daca ajungem la un arbore gol, inseamna ca
  ;; nu s-a gasi tun rezultat si returnam #f
  (if (collection-empty? ST) #f
      ;; altfel
      (cond
        ;; daca lungimea subsirului este indeajuns de mare
        ;; pentru a acoperi lungimea cautata
        ((>= (length acc) len)
         ;; returnam lista formata din primele len caractere
         ;; ale subsirului gasit
         ;; deci s-a gasit solutie!
         (take acc len))
      (else
       ;; daca avem subsir prea scurt
       (let* ((label (get-branch-label (first-branch ST)))
              (subtree (get-branch-subtree (first-branch ST)))
              ;; apelam functia pentru subsirul la care am lipit
              ;; labelul curent
              (result (repeated-substring subtree len (append acc label))))
         ;; daca am gasit un rezultat valid (diferit de #f)
         (if result
             ;; il returnam
             result
             ;; altfel, cautam in celelalte branch-uri
             (repeated-substring (other-branches ST) len acc)))
       )
       )
      )
  )