#ifndef __TARGET_H__
#define __TARGET_H__

#include <cstdarg>
#include <cstdio>
#include <algorithm>
#include <list>
#include <string>

// This class abstracts the target location for output.
// It is used to allow the same functions to generate strings
// to a file or to a buffer.
class Target
{
private:
  std::list<std::string> errors;

public:
  Target() : errors(std::list<std::string>()) {};
  virtual ~Target() { handle_errors(); };

  void add_error(const char* error) {
    errors.push_front(error);
  };

  void handle_errors() {
    while(!errors.empty()) {
      printf("Output error: %s", errors.front().c_str());
      errors.pop_front();
    }
  }

  virtual void write_char(char c) = 0;
  virtual void write_char(char c, unsigned int count) = 0;
  virtual void write_string(const char* fmt ...) = 0;
  virtual void write_data(const void* data, unsigned int size, unsigned int num) = 0;
};

// Send output to a file
class FileTarget : public Target
{
private:
  FILE* out;
public:
  FileTarget(FILE* file_ptr);
  ~FileTarget();
  void write_char(char c);
  void write_char(char c, unsigned int count);
  void write_string(const char* fmt ...);
  void write_data(const void* data, unsigned int size, unsigned int num);
};

// Capture output in a string
class BufferTarget : public Target
{
private:
  char* buffer;
  unsigned int buf_size;
  unsigned int start;
  unsigned int end;
public:
  BufferTarget(unsigned int size);
  ~BufferTarget();
  void write_char(char c);
  void write_char(char c, unsigned int count);
  void write_string(const char* fmt ...);
  void write_data(const void* data, unsigned int size, unsigned int num);
  const char* str();
  unsigned int length() const;
};

#endif /* __TARGET_H__ */
