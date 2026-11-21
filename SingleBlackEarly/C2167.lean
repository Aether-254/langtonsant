import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2167 : checkSingleBlackFast (-85, -67) 13880 .north (32, 24) (-58, -40) = true := by
  decide +kernel

end LangtonsAnt
