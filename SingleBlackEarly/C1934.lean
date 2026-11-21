import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1934 : checkSingleBlackFast2 (-67, -45) 16209 .west (21, 30) (-50, 10) = true := by
  decide +kernel

end LangtonsAnt
