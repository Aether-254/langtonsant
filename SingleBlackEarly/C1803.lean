import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1803 : checkSingleBlackFast (-56, -33) 14159 .west (15, 25) (-44, 5) = true := by
  decide +kernel

end LangtonsAnt
