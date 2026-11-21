import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0915 : checkSingleBlackFast (-9, 4) 26615 .west (-9, -1) (-32, -7) = true := by
  decide +kernel

end LangtonsAnt
