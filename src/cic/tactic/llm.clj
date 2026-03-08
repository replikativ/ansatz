;; Copyright (c) 2026 Simmis GmbH. All rights reserved.
;; Tactic layer — LLM client for Fireworks/OpenAI-compatible APIs.

(ns cic.tactic.llm
  "Minimal HTTP client for OpenAI-compatible LLM APIs (Fireworks, etc.).
   Uses Java's built-in HttpClient to avoid external dependencies."
  (:require [clojure.data.json :as json])
  (:import [java.net URI]
           [java.net.http HttpClient HttpRequest HttpRequest$BodyPublishers
                          HttpResponse HttpResponse$BodyHandlers]
           [java.time Duration]))

;; ============================================================
;; Configuration
;; ============================================================

(def default-config
  {:base-url "https://api.fireworks.ai/inference/v1"
   :model "accounts/fireworks/models/glm-5"
   :max-tokens 1024
   :temperature 0.3})

(defonce ^:private http-client
  (delay (-> (HttpClient/newBuilder)
             (.connectTimeout (Duration/ofSeconds 30))
             (.build))))

(defn make-config
  "Create an LLM config, merging with defaults.
   API key is read from FIREWORKS_API_KEY env var if not provided."
  [overrides]
  (let [cfg (merge default-config overrides)
        api-key (or (:api-key cfg)
                    (System/getenv "FIREWORKS_API_KEY")
                    (System/getenv "OPENAI_API_KEY"))
        base-url (or (:base-url cfg)
                     (System/getenv "OPENAI_BASE_URL")
                     (:base-url default-config))]
    (when-not api-key
      (throw (ex-info "API key required. Set FIREWORKS_API_KEY or OPENAI_API_KEY env var."
                      {:env ["FIREWORKS_API_KEY" "OPENAI_API_KEY"]})))
    (assoc cfg :api-key api-key :base-url base-url)))

;; ============================================================
;; HTTP request
;; ============================================================

(defn- build-request-body
  "Build the JSON request body for chat completions."
  [config messages]
  (json/write-str
   (cond-> {:model (:model config)
            :max_tokens (:max-tokens config)
            :messages messages}
     (:temperature config) (assoc :temperature (:temperature config))
     (:top-p config) (assoc :top_p (:top-p config)))))

(defn chat-completion
  "Send a chat completion request. Returns the response content string.

   Args:
     config   - LLM config map (from make-config)
     messages - Vector of {:role \"user\"/\"system\"/\"assistant\" :content \"...\"}

   Returns:
     {:content string, :usage {:input-tokens N :output-tokens M}}"
  [config messages]
  (let [url (str (:base-url config) "/chat/completions")
        body (build-request-body config messages)
        request (-> (HttpRequest/newBuilder)
                    (.uri (URI/create url))
                    (.header "Authorization" (str "Bearer " (:api-key config)))
                    (.header "Content-Type" "application/json")
                    (.POST (HttpRequest$BodyPublishers/ofString body))
                    (.timeout (Duration/ofSeconds 60))
                    (.build))
        response (.send ^HttpClient @http-client request
                        (HttpResponse$BodyHandlers/ofString))
        status (.statusCode response)]
    (when (>= status 400)
      (throw (ex-info (str "LLM API error " status)
                      {:status status
                       :body (.body response)})))
    (let [parsed (json/read-str (.body response) :key-fn keyword)
          choice (first (:choices parsed))
          usage (:usage parsed)]
      {:content (get-in choice [:message :content])
       :usage {:input-tokens (:prompt_tokens usage)
               :output-tokens (:completion_tokens usage)}
       :model (:model parsed)})))

(defn quick-chat
  "One-shot chat with a user prompt. Returns the content string."
  [config prompt]
  (:content (chat-completion config [{:role "user" :content prompt}])))

(defn chat-with-system
  "Chat with a system prompt and user prompt."
  [config system-prompt user-prompt]
  (:content (chat-completion config [{:role "system" :content system-prompt}
                                     {:role "user" :content user-prompt}])))
