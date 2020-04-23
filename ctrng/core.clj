(ns ctrng.core
  (:require
   [clojure.math.combinatorics]
   [korma.core :as korma]
   [cheshire.core :as json]
   ))

(defn- reset-board-map [m]
  (let [keys (flatten (map (fn [x] (map #(str %1 %2) (map str (seq "abcdefgh")) (repeat 8 x))) (range 1 9)))]
    (into m (map vector keys (repeat 64 nil)))))

(defn- piece [p colour]
  (first
   (filter p
           (filter colour
                   (flatten
                    (map #(for [n [:king :queen :bishop :knight :rook :pawn]]
                                            {n true
                                             % true}) [:white :black]))))))

(defn- init-in-map [p colour m]
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

(defn- init-map [lst m]
  (if (empty? lst)
    m
    (recur (nnext lst) (merge m (init-in-map (first lst) (second lst) {})))))

(defn- init-pawns [p colour m]
  (let [rows {:white "2"
              :black "7"}
        indexes {:pawn (map str (seq "abcdefgh"))}
        fun (fn [p c] (for [xs (indexes p)]
                        (str xs (rows c))))]
    (apply merge (map #(assoc m % (piece p colour)) (fun p colour)))))

(defn- init-board []
  (merge (init-map
          (interleave (flatten (repeat 2 [:rook :knight :bishop :king :queen])) (flatten (repeat 10 [:black :white])))
          (reset-board-map {}))
         (apply merge (map #(init-pawns :pawn % {}) [:black :white]))))

(def boardsdb (korma.db/sqlite3 {:db "../dbs/boards"}))

(korma.db/defdb boards boardsdb)

(korma/defentity boardgames)

(defn select-chessboard [game]
  "Returns JSON. Does not convert JSON to Clojure maps"
  (first (korma/select boardgames (korma/where (= :gid game)))))

(defn- insert-chessmap [game m]
  (korma/insert boardgames (korma/values {:gid game
                                          :gmap (json/generate-string m)})))

(defn- update-chessboard [game m]
  (korma/update boardgames (korma/where (= :gid game)) (korma/set-fields {:gmap (json/generate-string m)})))

(defn- chessmap [game]
  (into {}
        (for [a (json/parse-string (:gmap (select-chessboard game)))]
          [(first a) (clojure.walk/keywordize-keys (second a))])))

(defn start-game! []
  (let [id (str (java.util.UUID/randomUUID))]
    (do
      (insert-chessmap id (init-board))
      (select-chessboard id))))

(defn- adversary [player]
  ({:white :black :black :white} player))

(defn- own? [game coord player]
  (try
    ((game coord) player)
    (catch Exception e nil)))

(defn- enemy? [game coord player]
  (try
    ((game coord) (adversary player))
    (catch Exception e nil)))

(defn- what [game coord]
  (try
    (game coord)
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

(defn- own-king [game player]
  (let [own-pieces (filter #(own? game % player) (keys game))]
    (first (filter #(= (what game %) {:king true player true}) own-pieces))))

(defn- maybe-potential-moves [mode game player src]
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
                              (if (= mode :normal) [x x-left-diag x-right-diag] [x-left-diag x-right-diag])
                              (and (not (or (own? game x player) (enemy? game x player)))
                                   (enemy? game x-left-diag player))
                              (if (= mode :normal) [x x-left-diag] [x-left-diag])
                              (and (not (or (own? game x player) (enemy? game x player)))
                                   (enemy? game x-right-diag player))
                              (if (= mode :normal) [x x-right-diag] [x-right-diag])
                              :else
                              (if (= mode :normal) [x] [])))
        :else nil)
      nil)))

(defn- enemy-potential [game player]
  (let
      [enemy-pieces (filter #(own? game % (adversary player)) (keys game))
       enemy-potential (distinct (flatten (map #(maybe-potential-moves :attack game (adversary player) %) enemy-pieces)))]
    (apply vector enemy-potential)))

(defn- potential-moves [game player src]
  (if (= src (own-king game player))
    (apply vector (clojure.set/difference (set (maybe-potential-moves :normal game player src))
                                          (set (enemy-potential game player))))
    (apply vector (maybe-potential-moves :normal game player src))))

(defn- check? [game player]
  (let [own-pieces (filter #(own? game % player) (keys game))
        own-potential (distinct (flatten (map #(potential-moves game player %) own-pieces)))
        chck? (some #(= (what game %) {:king true
                                       (adversary player) true}) own-potential) ]
    chck?))

(defn- check-e? [game player]
  (let [own-pieces (filter #(own? game % player) (keys game))
        enemy-pot (enemy-potential game player)
        chck? (some #(= (what game %) {:king true
                                       player true}) enemy-pot) ]
    chck?))

(defn- under-check? [game player]
  ;;(check? game (adversary player))
  (check-e? game player))

(defn- test-move [game player dest]
  (let [src (own-king game player)
        pot-moves (potential-moves game player src)]
    (if (some #(= % dest) pot-moves)
      (let [pre-testmap (assoc game dest (what game src))
            testmap (assoc pre-testmap src nil)]
        (if (under-check? testmap player)
          nil
          true))
      nil)))

(defn- test-next-move [game player src dest]
  (let [pot-moves (potential-moves game player src)]
    (if (some #(= % dest) pot-moves)
      (let [pre-testmap (assoc game dest (what game src))
            testmap (assoc pre-testmap src nil)]
        (if (under-check? testmap player)
          nil
          true))
      nil)))

(defn- run-test-moves [game player pot-moves acc]
  (if (empty? pot-moves)
    acc
    (recur game player (next pot-moves) (conj acc (test-move game player (first pot-moves))))))
  
(defn- checkmate? [game player]
  (or (and (under-check? game player) (empty? (potential-moves game player (own-king game player))))
      (and (under-check? game player) (every? nil? (run-test-moves game player (potential-moves game player (own-king game player)) [])))))

(defn- pawn? [piece]
  (piece :pawn))

(defn- promotions [game player]
  (let [own-pieces (filter #(own? game % player) (keys game))
        last-row (map #(str %1 %2) (map str (seq "abcdefgh")) (repeat 8 (if (= :white player) 8 1)))]
    (apply vector (filter pawn? (map #(game %) (filter (set last-row) own-pieces))))))

(defn- promotion? [game player] (seq (promotions game player)))

(defn chosen [chs clr]
  (let [opts {"rook" {:rook true (keyword clr) true}
              "queen" {:queen true (keyword clr) true}
              "knight" {:knight true (keyword clr) true}
              "bishop" {:bishop true (keyword clr) true}}]
    (opts chs)))

(defn promote! [game player dest promoted]
  (let [oldboard (chessmap game)
        midboard (dissoc oldboard "promotion")
        newboard (assoc midboard dest promoted)]
    (update-chessboard game newboard)))

(defn- post-move [game player]
  (cond  (check? game player) (if (checkmate? game (adversary player))
                                (assoc game :checkmate true)
                                (assoc game :check true))
         (promotion? game player) (assoc game :promotion (promotions game player))
         :else game))

(defn move-piece! [game player src dest]
  (let [m (dissoc (chessmap game) "check")
        piece-to-move (what m src)]
    (if (test-next-move m player src dest)
      (let [pre-newmap (assoc m dest piece-to-move)
            newmap (assoc pre-newmap src nil)]
        (update-chessboard game (post-move newmap player)))
      nil)))
