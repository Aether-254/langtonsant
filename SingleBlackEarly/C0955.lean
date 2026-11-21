import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0955 : checkSingleBlackFast (8, 17) 9767 .east (-6, -5) (-24, -6) = true := by
  decide +kernel

end LangtonsAnt
