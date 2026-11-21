import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2195 : checkSingleBlackFast (-93, -65) 26465 .east (42, 30) (20, -65) = true := by
  decide +kernel

end LangtonsAnt
