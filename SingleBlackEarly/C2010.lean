import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2010 : checkSingleBlackFast (-72, -54) 29187 .east (39, 27) (-2, -49) = true := by
  decide +kernel

end LangtonsAnt
