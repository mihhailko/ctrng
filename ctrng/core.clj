(ns ctrng.core)

(load-file "math/combinatorics.cljc")

(defn reset-board-map [m]
  (let [keys (flatten (map (fn [x] (map #(str %1 %2) (map str (seq "abcdefgh")) (repeat 8 x))) (range 1 9)))]
    (into m (map vector keys (repeat 64 nil)))))

(defn piece [p colour]
  (first
   (filter p
           (filter colour
                   (flatten
                    (map #(for [n [:king :queen :bishop :knight :rook :pawn]]
                                            {n true
                                             % true}) [:white :black]))))))

(defn init-in-map [p colour m]
  (let [rows {:white "1"
              :black "8"}
        indexes {:rook ["a" "h"]
                 :knight ["b" "g"]
                 :bishop ["c" "f"]
                 :king ["e"]
                 :queen ["d"]}
        fun (fn [p c] (for [xs (indexes p)]
                        (str xs (rows c))))]
    (apply merge (map #(assoc m % (piece p colour)) (fun p colour)))))

(defn init-map [lst m]
  (if (empty? lst)
    m
    (recur (nnext lst) (merge m (init-in-map (first lst) (second lst) {})))))

(defn init-pawns [p colour m]
  (let [rows {:white "2"
              :black "7"}
        indexes {:pawn (map str (seq "abcdefgh"))}
        fun (fn [p c] (for [xs (indexes p)]
                        (str xs (rows c))))]
    (apply merge (map #(assoc m % (piece p colour)) (fun p colour)))))

(defn init-board []
  (merge (init-map
          (interleave (flatten (repeat 2 [:rook :knight :bishop :king :queen])) (flatten (repeat 10 [:black :white])))
          (reset-board-map {}))
         (apply merge (map #(init-pawns :pawn % {}) [:black :white]))))

(def chessboard (atom {}))

(defn start-game! []
  (let [id (str (java.util.UUID/randomUUID))]
    (swap! chessboard assoc id (init-board))
    (println id)))

(defn adversary [player]
  ({:white :black :black :white} player))

(defn own? [game coord player]
  (try
    ((((deref chessboard) game) coord) player)
    (catch Exception e nil)))

(defn enemy? [game coord player]
  (try
    ((((deref chessboard) game) coord) (adversary player))
    (catch Exception e nil)))

(defn what [game coord]
  (try
    (((deref chessboard) game) coord)
    (catch Exception e nil)))

(defn- moves-args [piece direct]
  (let [tower-as (repeat 16 0)
        tower-bs (range -7 8)
        xy {:knight [1 2]
            :bishop [2 2]
            :king [1 1]
            :queen [1 1]
            :rook [0 0]}
        x (first (xy piece))
        y (second (xy piece))
        pairs {:diag (clojure.math.combinatorics/permutations [x y (- x) (- y)])
               :vert (clojure.math.combinatorics/permutations [0 0 x (- y)])
               :horiz (clojure.math.combinatorics/permutations [0 (- x) y])
               :rook (partition 2 (flatten [(map vector tower-as tower-bs) (map vector tower-bs tower-as)]))}
        removes {:knight {:diag #(= (first %) (- (second %)))}
                 :bishop {:diag (fn [n] nil)}
                 :king {:diag (fn [n] nil)
                        :vert (fn [n] (or (= (first n) (second n)) (not (= 0 (first n)))))
                        :horiz (fn [n] (or (= (first n) (second n)) (not (= 0 (second n)))))}
                 :queen {:diag (fn [n] nil)}
                 :rook {:rook (fn [n] (= n (xy piece)))}}]
    (remove ((removes piece) direct) (distinct (partition 2 (flatten (pairs direct)))))))

(defn own-king [game player]
  (let [board ((deref chessboard) game)
        own-pieces (filter #(own? game % player) (keys board))]
    (first (filter #(= (what game %) {:king true player true}) own-pieces))))

(defn- maybe-potential-moves [game player src]
  (let [alpha-to-int (into {} (map vector (seq "abcdefgh") (range 1 9)))
        int-to-alpha (clojure.set/map-invert alpha-to-int)
        piece (what game src)
        alpha (first (seq src))
        seq-coord-letter (str (first (seq src)))
        seq-coord-digit (Integer/parseInt (str (second (seq src))))
        x-inc (if (< seq-coord-digit 8) (str (str seq-coord-letter) (inc seq-coord-digit)) nil)
        x-dec (if (> seq-coord-digit 1) (str (str seq-coord-letter) (dec seq-coord-digit)) nil)
        piece-fun #(str (str (int-to-alpha (+ (alpha-to-int alpha) (first %)))) (+ (second %) seq-coord-digit))
        filter-fun #(and (not (own? game % player)) (contains? (reset-board-map {}) %))
        x-left-diag-inc (piece-fun [-1 1])
        x-right-diag-inc (piece-fun [1 1])
        x-left-diag-dec (piece-fun [-1 -1])
        x-right-diag-dec (piece-fun [1 -1])
        knight-moves (map piece-fun (moves-args :knight :diag))
        bishop-moves (map piece-fun (moves-args :bishop :diag))
        king-moves (map piece-fun (partition 2 (flatten (map #(moves-args :king %) [:vert :diag :horiz]))))
        queen-moves (map piece-fun (moves-args :queen :diag))
        rook-moves-pre (map piece-fun (moves-args :rook :rook))
        rook-moves-post (let [pairs (partition 7 rook-moves-pre)
                               frst (reverse (first pairs))
                               scnd (first (next pairs))
                               thrd (reverse (first (nnext pairs)))
                               frth (last pairs)]
                           [frst scnd thrd frth])]
    (if (own? game src player)
      (cond
        (piece :rook) (let [pre (for [t rook-moves-post]
                                  (take-while #(not (own? game % player)) t))
                            mid (map count (for [p pre]
                                               (take-while #(and (not (enemy? game % player)) 
                                                                 (contains? (reset-board-map {}) %)) p)))
                            post (filter #(contains? (reset-board-map {}) %)
                                         (flatten (map #(take (inc %1) %2) mid pre)))]
                         post)
        (piece :queen) (filter filter-fun queen-moves)
        (piece :king) (filter filter-fun king-moves)
        (piece :bishop) (filter filter-fun bishop-moves)
        (piece :knight) (filter filter-fun knight-moves)
        (piece :pawn) (let [x (if (= :white player) x-inc x-dec)
                            x-left-diag (if (= :white player) x-left-diag-inc x-right-diag-dec)
                            x-right-diag (if (= :white player) x-right-diag-inc x-left-diag-dec)]
                        (cond (and (or (own? game x player) (enemy? game x player))
                                   (and (enemy? game x-left-diag player) (enemy? game x-right-diag player)))
                              [x-left-diag x-right-diag]
                              (and (or (own? game x player) (enemy? game x player))
                                   (enemy? game x-left-diag player))
                              [x-left-diag]
                              (and (or (own? game x player) (enemy? game x player))
                                   (enemy? game x-right-diag player))
                              [x-right-diag]
                              (and (not (or (own? game x player) (enemy? game x player)))
                                   (and (enemy? game x-left-diag player) (enemy? game x-right-diag player)))
                              [x x-left-diag x-right-diag]
                              (and (not (or (own? game x player) (enemy? game x player)))
                                   (enemy? game x-left-diag player))
                              [x x-left-diag]
                              (and (not (or (own? game x player) (enemy? game x player)))
                                   (enemy? game x-right-diag player))
                              [x x-right-diag]
                              :else
                              [x]))
        :else nil)
      nil)))

(defn enemy-potential [game player]
  (let [board ((deref chessboard) game)
        enemy-pieces (filter #(own? game % (adversary player)) (keys board))
        enemy-potential (distinct (flatten (map #(maybe-potential-moves game (adversary player) %) enemy-pieces)))]
    (apply vector enemy-potential)))

(defn potential-moves [game player src]
  (if (= src (own-king game player))
    (apply vector (clojure.set/difference (maybe-potential-moves game player src)
                                          (enemy-potential game player)))
    (apply vector (maybe-potential-moves game player src))))

(defn check? [game player]
  (let [board ((deref chessboard) game)
        own-pieces (filter #(own? game % player) (keys board))
        own-potential (distinct (flatten (map #(potential-moves game player %) own-pieces)))
        chck? (some #(= (what game %) {:king true
                                       (adversary player) true}) own-potential) ]
    chck?))

(defn under-check? [game player]
  (check? game (adversary player)))

(defn test-move! [game player dest]
  (let [src (own-king game player)
        pot-moves (potential-moves game player src)]
    (if (some #(= % dest) pot-moves)
      (do
        (swap! chessboard assoc (str "test-" game) ((deref chessboard) game))
        (swap! chessboard assoc-in [(str "test-" game) dest] (what game src))
        (swap! chessboard assoc-in [(str "test-" game) src] nil)
        (if (under-check? (str "test-" game) player)
          nil
          true))
      nil)))

(defn run-test-moves! [game player pot-moves acc]
  (if (empty? pot-moves)
    acc
    (recur game player (next pot-moves) (conj acc (test-move! game player (first pot-moves))))))
  
(defn checkmate? [game player]
  (or (and (under-check? game player) (empty? (potential-moves game player (own-king game player))))
      (and (under-check? game player) (every? nil? (run-test-moves! game player (potential-moves game player (own-king game player)) [])))))

(defn post-move [game player m]
  (cond (checkmate? game (adversary player)) (assoc m :checkmate true)
        (check? game player) (assoc m :check true)
        :else m))

(defn move-piece! [game player src dest]
  (let [piece-to-move (what game src)
        pot-moves (potential-moves game player src)]
    (if (some #(= % dest) pot-moves)
      (do
        (swap! chessboard assoc (str "test-" game) ((deref chessboard) game))
        (swap! chessboard assoc-in [(str "test-" game) dest] piece-to-move)
        (swap! chessboard assoc-in [(str "test-" game) src] nil)
        (if (under-check? (str "test-" game) player)
          nil
          (do (swap! chessboard assoc-in [game dest] piece-to-move)
              (swap! chessboard assoc-in [game src] nil)
              (post-move game player {:chessboard ((deref chessboard) game)}))))
      nil)))

;;(start-game!)

;;(enemy-potential "9f10c53d-dde9-4fc9-90fd-e57a8c2957cb" :white)

;;(own-king "de9efe42-19cf-4112-ab02-fdde57c89d37" :black)

;;(potential-moves "9f10c53d-dde9-4fc9-90fd-e57a8c2957cb" :black "d8")

;;(potential-moves "de9efe42-19cf-4112-ab02-fdde57c89d37" :white "g4")

;;(move-piece! "9f10c53d-dde9-4fc9-90fd-e57a8c2957cb" :black "c6" "c5")

;;(checkmate? "de9efe42-19cf-4112-ab02-fdde57c89d37" :black)

;;(what "de9efe42-19cf-4112-ab02-fdde57c89d37" "e4")

;;(under-check? "de9efe42-19cf-4112-ab02-fdde57c89d37" :black)



        
