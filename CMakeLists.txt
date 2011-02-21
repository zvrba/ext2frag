PROJECT(ext2frag)
SET(CMAKE_BUILD_TYPE Release)

FIND_PACKAGE(Boost)

FIND_PATH(E2FS_INCDIR ext2fs/ext2fs.h /usr/include /usr/local/include)
FIND_LIBRARY(E2FS_LIB ext2fs /usr/lib /usr/local/lib)

#
# shared libs automatically link in com_err.so, but not static 
#
GET_FILENAME_COMPONENT(TMP ${E2FS_LIB} EXT)
IF(${TMP} STREQUAL ".a") 
	FIND_LIBRARY(COMERR_LIB com_err /usr/lib /usr/local/lib)
ENDIF(${TMP} STREQUAL ".a")

INCLUDE_DIRECTORIES(${Boost_INCLUDE_DIRS} ${E2FS_INCDIR})
ADD_EXECUTABLE(ext2frag ext2frag.cc)
TARGET_LINK_LIBRARIES(ext2frag ${E2FS_LIB})
IF(COMERR_LIB)
	TARGET_LINK_LIBRARIES(ext2frag ${COMERR_LIB})
ENDIF(COMERR_LIB)
