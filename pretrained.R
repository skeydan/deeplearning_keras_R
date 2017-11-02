library(keras)
library(EBImage)

#model <- application_resnet50(weights = 'imagenet')
model <- application_vgg16(weights = 'imagenet')
#model <- application_inception_v3(weights = 'imagenet')

img_path <- "cx.jpg"
img <- image_load(img_path, target_size = c(224,224)) # vgg, resnet
# img <- image_load(img_path, target_size = c(299,299)) # inception
x <- image_to_array(img)
dim(x) <- c(1, dim(x))
dim(x)

display(readImage(img_path), method="raster", all = TRUE)


x <- imagenet_preprocess_input(x) # vgg, resnet
#x <- inception_v3_preprocess_input(x) # inception

# make predictions then decode and print them
preds <- model %>% predict(x)
which.max(preds)
imagenet_decode_predictions(preds)

