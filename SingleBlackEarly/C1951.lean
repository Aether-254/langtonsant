import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1951 : checkSingleBlackFast (-70, -44) 13148 .north (24, 16) (-50, -32) = true := by
  decide +kernel

end LangtonsAnt
