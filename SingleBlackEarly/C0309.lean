import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0309 : checkSingleBlackFast (4, 11) 25153 .west (-8, 6) (-32, -9) = true := by
  decide +kernel

end LangtonsAnt
