import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1049 : checkSingleBlackFast (-11, -5) 76060 .south (11, -32) (-31, -52) = true := by
  decide +kernel

end LangtonsAnt
