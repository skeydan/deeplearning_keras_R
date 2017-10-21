library(keras)
library(ggplot2)
library(tidyr)

x_train <- iris[1:120, "Petal.Length"]
y_train <- iris[1:120, "Petal.Width"]
x_test <- iris[121:150, "Petal.Length"]
y_test <- iris[121:150, "Petal.Width"]


model <- keras_model_sequential()
model %>% 
  layer_dense(units = 16, activation = "relu", input_shape = 1) %>%
  layer_dense(units = 1) # linear activation

model %>% summary()

model %>% compile(optimizer = "adam", loss = "mean_squared_error")

hist <- model %>% fit(x_train, y_train, batch_size = 10, validation_split = 0.1, epochs = 100)

plot(hist)

model %>% evaluate(x_test, y_test)

preds <- model %>% predict(x_test)
preds
preds_df <- data.frame(predictor = x_test, actual = y_test, predicted = preds)
preds_df <- preds_df %>% gather(type, value, -predictor)
preds_df
ggplot(preds_df, aes(x = predictor, y = value)) + geom_point(aes(color = type))