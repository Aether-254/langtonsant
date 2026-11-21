import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1388 : checkSingleBlackFast (-19, 4) 20017 .east (-4, -8) (-28, -25) = true := by
  decide +kernel

end LangtonsAnt
