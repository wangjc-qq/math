#!/bin/bash

echo "===== Homebrew 镜像配置检查 ====="
echo

# 检查 brew.git 镜像
echo "1. brew.git 镜像:"
git -C "$(brew --repo)" remote -v
echo

# 检查 homebrew-core.git 镜像
echo "2. homebrew-core.git 镜像:"
git -C "$(brew --repo homebrew/core)" remote -v
echo

# 检查 homebrew-cask.git 镜像
echo "3. homebrew-cask.git 镜像:"
git -C "$(brew --repo homebrew/cask)" remote -v
echo

# 检查 bottles 镜像
echo "4. Bottles 镜像:"
if [ -n "$HOMEBREW_BOTTLE_DOMAIN" ]; then
    echo "当前设置: $HOMEBREW_BOTTLE_DOMAIN"
else
    echo "未设置 Bottles 镜像 (使用默认源)"
fi

# 检查配置文件
echo
echo "5. 配置文件中的设置:"
echo "   - ~/.zshrc:"
grep -i 'homebrew' ~/.zshrc 2>/dev/null || echo "   未找到相关配置"
echo "   - ~/.bash_profile:"
grep -i 'homebrew' ~/.bash_profile 2>/dev/null || echo "   未找到相关配置"
